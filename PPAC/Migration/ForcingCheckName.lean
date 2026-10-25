/- Pinned ForcingNames.lean:184-201, the original membership-recursive checkName.
This is a specialized internal graph for that exact range equation. It consumes
existing native set induction, Collection/Separation, pair/product constructors,
and the accepted graph union/insertion lemmas. It does not assume external
WellFounded, introduce a generic recursion backend, or rebuild ordinal recursion. -/
import PPAC.Migration.ForcingUnionAction

namespace PPAC.Migration.ForcingCheckName
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Application of the existing full native membership-induction schema. -/
theorem formula_induction (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+1)) (params : Fin n → M.Carrier .set)
    (step : ∀ x, (∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y x →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases y params) p) →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x params) p) :
    ∀ x, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x params) p := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hi := (GodelDefOutput.close_semantics E _).mp
    ((Translation.realizes_sentence M _).mp ((SetInduction.native_induction p).semantically_entails M hM)) params
  change Formula.Realize E params (SetInductionSyntax.progressive p id) →
    Formula.Realize E params (SetInductionSyntax.holds p id) at hi
  exact (ForcingNameInduction.holds_semantics E params p id).mp
    (hi ((ForcingNameInduction.member_progressive_semantics E params p id).mpr step))

def covered {m : Nat} (g x : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) x.castSucc).imp
    (.ex (Source.SetLanguage.edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

def Covered (g x : M.Carrier .set) : Prop :=
  ∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y x → ∃ v, PureKuratowski.PairMember M y v g

def entry {m : Nat} (t x g z : Fin m) : Formula m :=
  .ex (.ex ((Formula.mem (Fin.last m).castSucc x.castSucc.castSucc).conj
    ((Source.SetLanguage.edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
      (PairSyntax.ordered z.castSucc.castSucc (Fin.last (m+1)) t.castSucc.castSucc))))

def Entry (t x g z : M.Carrier .set) : Prop :=
  ∃ y v, (Definitional.Project.FirstOrderSemantics.reduct M).mem y x ∧
    PureKuratowski.PairMember M y v g ∧ PureKuratowski.Code M z v t

def equation {m : Nat} (t x g output : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) output.castSucc).iff (entry t.castSucc x.castSucc g.castSucc (Fin.last m)))

def Equation (t x g output : M.Carrier .set) : Prop :=
  ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z output ↔ Entry t x g z

def good {m : Nat} (t g : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    ((covered g.castSucc.castSucc (Fin.last m).castSucc).conj
      (equation t.castSucc.castSucc (Fin.last m).castSucc g.castSucc.castSucc (Fin.last (m+1))))))

def Good (t g : M.Carrier .set) : Prop :=
  ∀ x output, PureKuratowski.PairMember M x output g → Covered g x ∧ Equation t x g output

def checkName {m : Nat} (t x output : Fin m) : Formula m :=
  .ex ((good t.castSucc (Fin.last m)).conj (Source.SetLanguage.edge (Fin.last m) x.castSucc output.castSucc))

def Checked (t x output : M.Carrier .set) : Prop :=
  ∃ g, Good t g ∧ PureKuratowski.PairMember M x output g

theorem covered_semantics {m : Nat} (v : Fin m → M.Carrier .set) (g x : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (covered g x) ↔ Covered (v g) (v x) := by
  simp only [covered, Formula.Realize, KuratowskiZF.source_edge, Fin.lastCases_last, Fin.lastCases_castSucc, Covered]
  rfl

theorem entry_semantics {m : Nat} (v : Fin m → M.Carrier .set) (t x g z : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (entry t x g z) ↔ Entry (v t) (v x) (v g) (v z) := by
  simp only [entry, Formula.Realize, KuratowskiZF.source_edge, KuratowskiZF.source_code,
    Fin.lastCases_last, Fin.lastCases_castSucc, Entry]
  rfl

theorem equation_semantics {m : Nat} (v : Fin m → M.Carrier .set) (t x g output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (equation t x g output) ↔
      Equation (v t) (v x) (v g) (v output) := by
  simp only [equation, Source.Formula.iff, Formula.Realize, entry_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc, Equation]
  exact forall_congr' (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)

theorem good_semantics {m : Nat} (v : Fin m → M.Carrier .set) (t g : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (good t g) ↔ Good (v t) (v g) := by
  simp only [good, Formula.Realize, KuratowskiZF.source_edge, covered_semantics (M := M),
    equation_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc, Good]
  rfl

theorem checkName_semantics {m : Nat} (v : Fin m → M.Carrier .set) (t x output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (checkName t x output) ↔
      Checked (v t) (v x) (v output) := by
  simp only [checkName, Formula.Realize, good_semantics (M := M), KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc, Checked]
  rfl

theorem compatible (hM : FirstOrder.Theory.Models M nativeZF) {t g h : M.Carrier .set}
    (hg : Good t g) (hh : Good t h) :
    ∀ x a b, PureKuratowski.PairMember M x a g → PureKuratowski.PairMember M x b h → a = b := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  let p := ForcingEvaluation.comparison (0 : Fin 3) 1 2
  let params : Fin 2 → M.Carrier .set := Fin.cases g (fun _ => h)
  have hp : ∀ x, Formula.Realize E (Fin.lastCases x params) p ↔
      ∀ a b, PureKuratowski.PairMember M x a g → PureKuratowski.PairMember M x b h → a = b := by
    intro x
    have he := ForcingEvaluation.comparison_semantics (M := M) (Fin.lastCases x params) (0 : Fin 3) 1 2
    have h0 : Fin.lastCases x params (0 : Fin 3) = g := (Fin.lastCases_castSucc (0 : Fin 2)).trans Fin.cases_zero
    have h1 : Fin.lastCases x params (1 : Fin 3) = h := (Fin.lastCases_castSucc (1 : Fin 2)).trans (Fin.cases_succ (0 : Fin 1))
    have h2 : Fin.lastCases x params (2 : Fin 3) = x := Fin.lastCases_last
    rw [h0, h1, h2] at he
    exact he
  have all := formula_induction hM p params (by
    intro x ih
    apply (hp x).mpr
    intro a b ha hb
    obtain ⟨ca, ea⟩ := hg x a ha
    obtain ⟨cb, eb⟩ := hh x b hb
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    constructor
    · intro hz
      obtain ⟨y, v, hy, hv, hCode⟩ := (ea z).mp hz
      obtain ⟨w, hw⟩ := cb y hy
      have heq := (hp y).mp (ih y hy) v w hv hw
      exact (eb z).mpr ⟨y, v, hy, heq.symm ▸ hw, hCode⟩
    · intro hz
      obtain ⟨y, w, hy, hw, hCode⟩ := (eb z).mp hz
      obtain ⟨v, hv⟩ := ca y hy
      have heq := (hp y).mp (ih y hy) v w hv hw
      exact (ea z).mpr ⟨y, w, hy, heq ▸ hv, hCode⟩)
  intro x
  exact (hp x).mp (all x)

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {t x a b : M.Carrier .set}
    (ha : Checked t x a) (hb : Checked t x b) : a = b := by
  obtain ⟨g, hg, ha⟩ := ha
  obtain ⟨h, hh, hb⟩ := hb
  exact compatible hM hg hh x a b ha hb

theorem equation_congr {t x g h output : M.Carrier .set}
    (ha : ∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y x →
      ∀ v, PureKuratowski.PairMember M y v g ↔ PureKuratowski.PairMember M y v h)
    (he : Equation t x g output) : Equation t x h output := by
  intro z
  apply (he z).trans
  constructor
  · rintro ⟨y, v, hy, hv, hc⟩
    exact ⟨y, v, hy, (ha y hy v).mp hv, hc⟩
  · rintro ⟨y, v, hy, hv, hc⟩
    exact ⟨y, v, hy, (ha y hy v).mpr hv, hc⟩

theorem union_good (hM : FirstOrder.Theory.Models M nativeZF) {t family U : M.Carrier .set}
    (hFamily : ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g family → Good t g)
    (hU : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z U ↔
      ∃ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g family ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem z g) : Good t U := by
  intro x output he
  obtain ⟨g, hg, hValue⟩ := (ForcingEvaluation.union_edge hU x output).mp he
  obtain ⟨hc, hEq⟩ := hFamily g hg x output hValue
  have ha : ∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y x →
      ∀ v, PureKuratowski.PairMember M y v g ↔ PureKuratowski.PairMember M y v U := by
    intro y hy v
    constructor
    · intro hv
      exact (ForcingEvaluation.union_edge hU y v).mpr ⟨g, hg, hv⟩
    · intro hv
      obtain ⟨h, hh, hvh⟩ := (ForcingEvaluation.union_edge hU y v).mp hv
      obtain ⟨w, hw⟩ := hc y hy
      have heq := compatible hM (hFamily h hh) (hFamily g hg) y v w hvh hw
      exact heq.symm ▸ hw
  refine ⟨?_, equation_congr ha hEq⟩
  intro y hy
  obtain ⟨v, hv⟩ := hc y hy
  exact ⟨v, (ha y hy v).mp hv⟩

def witness {m : Nat} (t x g : Fin m) : Formula m :=
  (good t g).conj (.ex (Source.SetLanguage.edge g.castSucc x.castSucc (Fin.last m)))

theorem witness_semantics {m : Nat} (v : Fin m → M.Carrier .set) (t x g : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (witness t x g) ↔
      Good (v t) (v g) ∧ ∃ output, PureKuratowski.PairMember M (v x) output (v g) := by
  simp only [witness, Formula.Realize, good_semantics (M := M), KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem collect_members (hM : FirstOrder.Theory.Models M nativeZF) (t x : M.Carrier .set)
    (ih : ∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y x → ∃ output, Checked t y output) :
    ∃ g, Good t g ∧ Covered g x := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  let params : Fin 1 → M.Carrier .set := fun _ => t
  let matrix := witness (0 : Fin 3) 1 2
  have hWitness : ∀ y, E y x → ∃ g, Good t g ∧ ∃ output, PureKuratowski.PairMember M y output g := by
    intro y hy
    obtain ⟨output, g, hg, he⟩ := ih y hy
    exact ⟨g, hg, output, he⟩
  have hc := (GodelDefOutput.close_semantics E (CollectionSyntax.core matrix)).mp
    ((Translation.realizes_sentence M _).mp ((CollectionSyntax.source_collection matrix).semantically_entails M hM)) params
  simp only [E, matrix, CollectionSyntax.core, Formula.Realize, DefinableMinimaChoice.realize_rename,
    witness_semantics (M := M), CollectionSyntax.firstIndex, CollectionSyntax.secondIndex,
    Fin.lastCases_last, Fin.lastCases_castSucc] at hc
  obtain ⟨family, hFamily⟩ := hc x hWitness
  let query := good (0 : Fin 2) 1
  have hSep := (GodelDefOutput.separation_semantics E query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨filtered, hFiltered⟩ := hSep params family
  have hf : ∀ g, E g filtered ↔ E g family ∧ Good t g := by
    intro g
    apply (hFiltered g).trans
    apply and_congr Iff.rfl
    exact good_semantics (M := M) (Fin.lastCases g params) 0 1
  obtain ⟨g, hg⟩ := SetTheory.KP.exists_union (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) filtered
  refine ⟨g, union_good hM (fun part hp => ((hf part).mp hp).2) hg, ?_⟩
  intro y hy
  obtain ⟨part, hPart, hGood, output, hv⟩ := hFamily y hy
  exact ⟨output, (ForcingEvaluation.union_edge hg y output).mpr ⟨part, (hf part).mpr ⟨hPart, hGood⟩, hv⟩⟩

theorem equation_exists (hM : FirstOrder.Theory.Models M nativeZF) (t x g : M.Carrier .set) :
    ∃ output, Equation t x g output := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨b, hb⟩ := ForcingMapConditions.coordinate_bound hM g
  obtain ⟨s, hs⟩ := SetTheory.KP.exists_singleton (SetTheory.ZF.modelsKP hZF) t
  obtain ⟨product, hProduct⟩ := SetTheory.ZF.exists_cartesianProduct hZF (KuratowskiZF.interpretation hM) b s
  let params : Fin 3 → M.Carrier .set := Fin.cases t (Fin.cases x (fun _ => g))
  let query := entry (0 : Fin 4) 1 2 3
  have hSep := (GodelDefOutput.separation_semantics E query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨output, hOutput⟩ := hSep params product
  have hQuery : ∀ z, Formula.Realize E (Fin.lastCases z params) query ↔ Entry t x g z := by
    intro z
    exact entry_semantics (M := M) (Fin.lastCases z params) 0 1 2 3
  refine ⟨output, fun z => ?_⟩
  constructor
  · intro hz
    exact (hQuery z).mp ((hOutput z).mp hz).2
  · intro hz
    obtain ⟨y, v, hy, hv, hCode⟩ := hz
    exact (hOutput z).mpr ⟨(hProduct z).mpr ⟨v, (hb y v hv).2, t, (hs t).mpr rfl, hCode⟩,
      (hQuery z).mpr ⟨y, v, hy, hv, hCode⟩⟩

theorem extend_good (hM : FirstOrder.Theory.Models M nativeZF) {t x g output extended : M.Carrier .set}
    (hg : Good t g) (hc : Covered g x) (hs : Equation t x g output)
    (he : ∀ y v, PureKuratowski.PairMember M y v extended ↔ PureKuratowski.PairMember M y v g ∨ (y = x ∧ v = output)) :
    Good t extended := by
  have hAgree : ∀ v, PureKuratowski.PairMember M x v g → v = output := by
    intro v hv
    exact (ModelTransfer.extensionality hM).eq_of_same_members v output
      (fun z => ((hg x v hv).2 z).trans (hs z).symm)
  have transfer : ∀ parent v, Covered g parent → Equation t parent g v → Covered extended parent ∧ Equation t parent extended v := by
    intro parent v hCover hEq
    have ha : ∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y parent →
        ∀ z, PureKuratowski.PairMember M y z g ↔ PureKuratowski.PairMember M y z extended := by
      intro y hy z
      constructor
      · intro hz
        exact (he y z).mpr (Or.inl hz)
      · intro hz
        rcases (he y z).mp hz with hOld | ⟨hY, hZ⟩
        · exact hOld
        · subst y
          subst z
          obtain ⟨w, hw⟩ := hCover x hy
          exact hAgree w hw ▸ hw
    refine ⟨?_, equation_congr ha hEq⟩
    intro y hy
    obtain ⟨z, hz⟩ := hCover y hy
    exact ⟨z, (ha y hy z).mp hz⟩
  intro parent v hv
  rcases (he parent v).mp hv with hOld | ⟨hParent, hV⟩
  · exact transfer parent v (hg parent v hOld).1 (hg parent v hOld).2
  · subst parent
    subst v
    exact transfer x output hc hs

theorem exists_checked (hM : FirstOrder.Theory.Models M nativeZF) (t x : M.Carrier .set) :
    ∃ output, Checked t x output := by
  let p : Formula 2 := .ex (checkName 0 1 2)
  let params : Fin 1 → M.Carrier .set := fun _ => t
  have hp : ∀ y, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases y params) p ↔
      ∃ output, Checked t y output := by
    intro y
    simp only [p, Formula.Realize, checkName_semantics (M := M)]
    rfl
  have all := formula_induction hM p params (by
    intro y ih
    apply (hp y).mpr
    obtain ⟨g, hg, hc⟩ := collect_members hM t y (fun z hz => (hp z).mp (ih z hz))
    obtain ⟨output, hs⟩ := equation_exists hM t y g
    obtain ⟨code, hCode⟩ := KuratowskiZF.exists_code hM y output
    obtain ⟨extended, hInsert⟩ := SetTheory.KP.exists_insert
      (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) g code
    have he := ForcingEvaluation.insert_edge hCode hInsert
    exact ⟨output, extended, extend_good hM hg hc hs he, (he y output).mpr (Or.inr ⟨rfl, rfl⟩)⟩)
  exact (hp x).mp (all x)

theorem mem_checkName (hM : FirstOrder.Theory.Models M nativeZF) {t x output : M.Carrier .set}
    (h : Checked t x output) (z : M.Carrier .set) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem z output ↔
      ∃ y v, (Definitional.Project.FirstOrderSemantics.reduct M).mem y x ∧ Checked t y v ∧ PureKuratowski.Code M z v t := by
  obtain ⟨g, hg, hValue⟩ := h
  obtain ⟨hc, hEq⟩ := hg x output hValue
  constructor
  · intro hz
    obtain ⟨y, v, hy, hv, hCode⟩ := (hEq z).mp hz
    exact ⟨y, v, hy, ⟨g, hg, hv⟩, hCode⟩
  · rintro ⟨y, v, hy, hv, hCode⟩
    obtain ⟨w, hw⟩ := hc y hy
    have heq := unique hM hv ⟨g, hg, hw⟩
    exact (hEq z).mpr ⟨y, v, hy, heq.symm ▸ hw, hCode⟩

theorem edge_checkName (hM : FirstOrder.Theory.Models M nativeZF) {t x output : M.Carrier .set}
    (h : Checked t x output) (child condition : M.Carrier .set) :
    PureKuratowski.PairMember M child condition output ↔
      ∃ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y x ∧ Checked t y child ∧ t = condition := by
  constructor
  · rintro ⟨z, hCode, hz⟩
    obtain ⟨y, v, hy, hv, hCode'⟩ := (mem_checkName hM h z).mp hz
    obtain ⟨hvEq, htEq⟩ := PureKuratowski.code_injective hCode hCode'
    exact ⟨y, hy, hvEq.symm ▸ hv, htEq.symm⟩
  · rintro ⟨y, hy, hv, ht⟩
    subst condition
    obtain ⟨z, hCode⟩ := KuratowskiZF.exists_code hM child t
    exact ⟨z, hCode, (mem_checkName hM h z).mpr ⟨y, child, hy, hv, hCode⟩⟩

def existenceSentence : Source.Sentence := (Formula.ex (checkName (0 : Fin 3) 1 2)).close

def uniquenessSentence : Source.Sentence :=
  ((checkName (0 : Fin 4) 1 2).imp ((checkName 0 1 3).imp (.equal 2 3))).close

def edgeSentence : Source.Sentence :=
  ((checkName (0 : Fin 5) 1 2).imp ((Source.SetLanguage.edge 2 3 4).iff
    (.ex ((Formula.mem 5 1).conj ((checkName 0 5 3).conj (.equal 0 4)))))).close

theorem existence_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence existenceSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  obtain ⟨output, h⟩ := exists_checked hM (v 0) (v 1)
  refine ⟨output, ?_⟩
  let env : Fin 3 → M.Carrier .set := Fin.lastCases output v
  exact (checkName_semantics (M := M) env 0 1 2).mpr h

theorem uniqueness_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence uniquenessSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hx hy
  exact unique hM ((checkName_semantics (M := M) v 0 1 2).mp hx) ((checkName_semantics (M := M) v 0 1 3).mp hy)

theorem edge_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence edgeSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  have he := edge_checkName hM ((checkName_semantics (M := M) v 0 1 2).mp h) (v 3) (v 4)
  have hl := KuratowskiZF.source_edge (M := M) v 2 3 4
  have hr : Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v
      (.ex ((Formula.mem 5 1).conj ((checkName 0 5 3).conj (.equal 0 4)))) ↔
      ∃ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y (v 1) ∧ Checked (v 0) y (v 3) ∧ v 0 = v 4 := by
    simp only [Formula.Realize, checkName_semantics (M := M)]
    rfl
  exact ⟨fun hz => hr.mpr (he.mp (hl.mp hz)), fun hz => hl.mpr (he.mpr (hr.mp hz))⟩

theorem existence_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  ModelTransfer.derives (fun _ hM => existence_models hM)
theorem uniqueness_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence uniquenessSentence) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models hM)
theorem edge_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence edgeSentence) :=
  ModelTransfer.derives (fun _ hM => edge_models hM)

/-- Exact original mem_checkName_iff, including the ordered-pair shape. -/
def membershipSentence : Source.Sentence :=
  ((checkName (0 : Fin 4) 1 2).imp ((Formula.mem 3 2).iff
    (.ex (.ex ((Formula.mem 4 1).conj ((checkName 0 4 5).conj (PairSyntax.ordered 3 5 0))))))).close

theorem membership_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence membershipSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  have he := mem_checkName hM ((checkName_semantics (M := M) v 0 1 2).mp h) (v 3)
  have hr : Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v
      (.ex (.ex ((Formula.mem 4 1).conj ((checkName 0 4 5).conj (PairSyntax.ordered 3 5 0))))) ↔
      ∃ y child, (Definitional.Project.FirstOrderSemantics.reduct M).mem y (v 1) ∧
        Checked (v 0) y child ∧ PureKuratowski.Code M (v 3) child (v 0) := by
    simp only [Formula.Realize, checkName_semantics (M := M), KuratowskiZF.source_code]
    rfl
  exact ⟨fun hz => hr.mpr (he.mp hz), fun hz => he.mpr (hr.mp hz)⟩

theorem membership_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence membershipSentence) :=
  ModelTransfer.derives (fun _ hM => membership_models hM)

end PPAC.Migration.ForcingCheckName
