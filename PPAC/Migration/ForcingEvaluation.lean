/- Object adaptation of pinned OpenAI Forcing/ForcingNames.lean:
evaluate, evaluate_eq, mem_evaluate_iff and evaluate_empty.
Internal graph witnesses implement the same range of active child values.
The graph is a set, not a host function; Child induction is the existing
nativeZF formula schema. No external WellFounded or standard omega is used. -/
import PPAC.Migration.ForcingNames

namespace PPAC.Migration.ForcingEvaluation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Exactly the existential clause in original mem_evaluate_iff, using a graph. -/
def activeValue {m : Nat} (G g sigma value : Fin m) : Formula m :=
  .ex (.ex ((Source.SetLanguage.edge sigma.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    ((Formula.mem (Fin.last (m+1)) G.castSucc.castSucc).conj
      (Source.SetLanguage.edge g.castSucc.castSucc (Fin.last m).castSucc value.castSucc.castSucc))))

def equation {m : Nat} (G g sigma value : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) value.castSucc).iff
    (activeValue G.castSucc g.castSucc sigma.castSucc (Fin.last m)))

def childrenCovered {m : Nat} (g sigma : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge sigma.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (.ex (Source.SetLanguage.edge g.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc (Fin.last (m+2))))))

def good {m : Nat} (G g : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    ((childrenCovered g.castSucc.castSucc (Fin.last m).castSucc).conj
      (equation G.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def evaluation {m : Nat} (G sigma value : Fin m) : Formula m :=
  .ex ((good G.castSucc (Fin.last m)).conj
    (Source.SetLanguage.edge (Fin.last m) sigma.castSucc value.castSucc))

def comparison {m : Nat} (g h sigma : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge g.castSucc.castSucc sigma.castSucc.castSucc (Fin.last m).castSucc).imp
    ((Source.SetLanguage.edge h.castSucc.castSucc sigma.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last m).castSucc (Fin.last (m+1))))))

def Equation (G g sigma value : M.Carrier .set) : Prop :=
  ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x value ↔
    ∃ tau condition, PureKuratowski.PairMember M tau condition sigma ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem condition G ∧
      PureKuratowski.PairMember M tau x g

def Covered (g sigma : M.Carrier .set) : Prop :=
  ∀ tau condition, PureKuratowski.PairMember M tau condition sigma →
    ∃ value, PureKuratowski.PairMember M tau value g

def Good (G g : M.Carrier .set) : Prop :=
  ∀ sigma value, PureKuratowski.PairMember M sigma value g → Covered g sigma ∧ Equation G g sigma value

def Evaluation (G sigma value : M.Carrier .set) : Prop :=
  ∃ g, Good G g ∧ PureKuratowski.PairMember M sigma value g

theorem activeValue_semantics {m : Nat} (v : Fin m → M.Carrier .set) (G g sigma value : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (activeValue G g sigma value) ↔
      ∃ tau condition, PureKuratowski.PairMember M tau condition (v sigma) ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition (v G) ∧
        PureKuratowski.PairMember M tau (v value) (v g) := by
  simp only [activeValue, Formula.Realize, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem equation_semantics {m : Nat} (v : Fin m → M.Carrier .set) (G g sigma value : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (equation G g sigma value) ↔
      Equation (v G) (v g) (v sigma) (v value) := by
  simp only [equation, Source.Formula.iff, Formula.Realize, activeValue_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc, Equation]
  exact forall_congr' (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)

theorem covered_semantics {m : Nat} (v : Fin m → M.Carrier .set) (g sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (childrenCovered g sigma) ↔
      Covered (v g) (v sigma) := by
  simp only [childrenCovered, Formula.Realize, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc, Covered]
  rfl

theorem good_semantics {m : Nat} (v : Fin m → M.Carrier .set) (G g : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (good G g) ↔
      Good (v G) (v g) := by
  simp only [good, Formula.Realize, KuratowskiZF.source_edge, covered_semantics (M := M),
    equation_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc, Good]
  rfl

theorem evaluation_semantics {m : Nat} (v : Fin m → M.Carrier .set) (G sigma value : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (evaluation G sigma value) ↔
      Evaluation (v G) (v sigma) (v value) := by
  simp only [evaluation, Formula.Realize, good_semantics (M := M), KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc, Evaluation]
  rfl

theorem comparison_semantics {m : Nat} (v : Fin m → M.Carrier .set) (g h sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (comparison g h sigma) ↔
      ∀ x y, PureKuratowski.PairMember M (v sigma) x (v g) →
        PureKuratowski.PairMember M (v sigma) y (v h) → x = y := by
  simp only [comparison, Formula.Realize, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

/-- Compatibility on overlapping domains, by the exact source Child induction. -/
theorem compatible (hM : FirstOrder.Theory.Models M nativeZF)
    {G g h : M.Carrier .set} (hg : Good G g) (hh : Good G h) :
    ∀ sigma x y, PureKuratowski.PairMember M sigma x g →
      PureKuratowski.PairMember M sigma y h → x = y := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  let p := comparison (0 : Fin 3) 1 2
  let v : Fin 2 → M.Carrier .set := Fin.cases g (fun _ => h)
  have hi := (GodelDefOutput.close_semantics E _).mp
    ((Translation.realizes_sentence M _).mp
      ((ForcingNameInduction.kernel_certificate p).semantically_entails M hM)) v
  change Formula.Realize E v (ForcingNameInduction.progressive p id) →
    Formula.Realize E v (SetInductionSyntax.holds p id) at hi
  have hc : ∀ sigma, Formula.Realize E (Fin.lastCases sigma v) p ↔
      ∀ x y, PureKuratowski.PairMember M sigma x g → PureKuratowski.PairMember M sigma y h → x = y := by
    intro sigma
    have hr := comparison_semantics (M := M) (Fin.lastCases sigma v) (0 : Fin 3) 1 2
    have h0 : Fin.lastCases sigma v (0 : Fin 3) = g :=
      (Fin.lastCases_castSucc (0 : Fin 2)).trans Fin.cases_zero
    have h1 : Fin.lastCases sigma v (1 : Fin 3) = h :=
      (Fin.lastCases_castSucc (1 : Fin 2)).trans (Fin.cases_succ (0 : Fin 1))
    have h2 : Fin.lastCases sigma v (2 : Fin 3) = sigma := Fin.lastCases_last
    rw [h0, h1, h2] at hr
    exact hr
  have hAll := hi ((ForcingNameInduction.progressive_semantics v p id).mpr (by
    intro sigma ih
    apply (hc sigma).mpr
    intro x y hx hy
    obtain ⟨cg, eg⟩ := hg sigma x hx
    obtain ⟨ch, eh⟩ := hh sigma y hy
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    constructor
    · intro hz
      obtain ⟨tau, condition, he, hCondition, hValue⟩ := (eg z).mp hz
      obtain ⟨w, hw⟩ := ch tau condition he
      have heq := (hc tau).mp (ih tau ⟨condition, he⟩) z w hValue hw
      exact (eh z).mpr ⟨tau, condition, he, hCondition, heq.symm ▸ hw⟩
    · intro hz
      obtain ⟨tau, condition, he, hCondition, hValue⟩ := (eh z).mp hz
      obtain ⟨w, hw⟩ := cg tau condition he
      have heq := (hc tau).mp (ih tau ⟨condition, he⟩) w z hw hValue
      exact (eg z).mpr ⟨tau, condition, he, hCondition, heq ▸ hw⟩))
  intro sigma
  exact (hc sigma).mp ((ForcingNameInduction.holds_semantics E v p id).mp hAll sigma)

theorem unique (hM : FirstOrder.Theory.Models M nativeZF)
    {G sigma x y : M.Carrier .set} (hx : Evaluation G sigma x) (hy : Evaluation G sigma y) : x = y := by
  obtain ⟨g, hg, hx⟩ := hx
  obtain ⟨h, hh, hy⟩ := hy
  exact compatible hM hg hh sigma x y hx hy

theorem union_edge {family U : M.Carrier .set}
    (hU : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x U ↔
      ∃ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem x part)
    (sigma value : M.Carrier .set) :
    PureKuratowski.PairMember M sigma value U ↔
      ∃ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family ∧
        PureKuratowski.PairMember M sigma value part := by
  constructor
  · rintro ⟨code, hCode, hMem⟩
    obtain ⟨part, hPart, hIn⟩ := (hU code).mp hMem
    exact ⟨part, hPart, code, hCode, hIn⟩
  · rintro ⟨part, hPart, code, hCode, hIn⟩
    exact ⟨code, hCode, (hU code).mpr ⟨part, hPart, hIn⟩⟩

/-- Union of compatible partial evaluation graphs obeys the same source equation. -/
theorem union_good (hM : FirstOrder.Theory.Models M nativeZF)
    {G family U : M.Carrier .set}
    (hFamily : ∀ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family → Good G part)
    (hU : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x U ↔
      ∃ part, (Definitional.Project.FirstOrderSemantics.reduct M).mem part family ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem x part) : Good G U := by
  intro sigma value he
  obtain ⟨part, hPart, hValue⟩ := (union_edge hU sigma value).mp he
  obtain ⟨hCover, hEquation⟩ := hFamily part hPart sigma value hValue
  constructor
  · intro tau condition hChild
    obtain ⟨v, hv⟩ := hCover tau condition hChild
    exact ⟨v, (union_edge hU tau v).mpr ⟨part, hPart, hv⟩⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨tau, condition, hChild, hCondition, hEval⟩ := (hEquation x).mp hx
      exact ⟨tau, condition, hChild, hCondition,
        (union_edge hU tau x).mpr ⟨part, hPart, hEval⟩⟩
    · rintro ⟨tau, condition, hChild, hCondition, hEval⟩
      obtain ⟨other, hOther, hOtherValue⟩ := (union_edge hU tau x).mp hEval
      obtain ⟨v, hv⟩ := hCover tau condition hChild
      have heq := compatible hM (hFamily other hOther) (hFamily part hPart) tau x v hOtherValue hv
      exact (hEquation x).mpr ⟨tau, condition, hChild, hCondition, heq.symm ▸ hv⟩

def entryWitness {m : Nat} (G z g : Fin m) : Formula m :=
  (good G g).conj (.all (.all ((PairSyntax.ordered z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1))).imp
      (.ex (Source.SetLanguage.edge g.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m+2)))))))

theorem entryWitness_semantics {m : Nat} (v : Fin m → M.Carrier .set) (G z g : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (entryWitness G z g) ↔
      Good (v G) (v g) ∧ ∀ tau condition, PureKuratowski.Code M (v z) tau condition →
        ∃ value, PureKuratowski.PairMember M tau value (v g) := by
  simp only [entryWitness, Formula.Realize, good_semantics (M := M), KuratowskiZF.source_code,
    KuratowskiZF.source_edge, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

/-- Existing Collection and Separation assemble child graphs; no choice function. -/
theorem collect_children (hM : FirstOrder.Theory.Models M nativeZF)
    (G sigma : M.Carrier .set)
    (ih : ∀ tau condition, PureKuratowski.PairMember M tau condition sigma →
      ∃ value, Evaluation G tau value) :
    ∃ g, Good G g ∧ Covered g sigma := by
  classical
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hKP := SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨empty, hEmpty⟩ := SetTheory.KP.exists_empty hKP
  have emptyGood : Good G empty := by
    intro tau value he
    obtain ⟨z, _, hz⟩ := he
    exact False.elim (hEmpty z hz)
  have hWitness : ∀ z, E z sigma → ∃ g, Good G g ∧
      ∀ tau condition, PureKuratowski.Code M z tau condition →
        ∃ value, PureKuratowski.PairMember M tau value g := by
    intro z hz
    by_cases he : ∃ tau condition, PureKuratowski.Code M z tau condition
    · obtain ⟨tau, condition, hCode⟩ := he
      obtain ⟨value, g, hg, hValue⟩ := ih tau condition ⟨z, hCode, hz⟩
      refine ⟨g, hg, ?_⟩
      intro tau' condition' hCode'
      obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hCode hCode'
      exact ⟨value, hValue⟩
    · exact ⟨empty, emptyGood, fun tau condition hCode => False.elim (he ⟨tau, condition, hCode⟩)⟩
  have hc := (GodelDefOutput.close_semantics E (CollectionSyntax.core (entryWitness (0 : Fin 3) 1 2))).mp
    ((Translation.realizes_sentence M _).mp
      ((CollectionSyntax.source_collection (entryWitness (0 : Fin 3) 1 2)).semantically_entails M hM)) (fun _ => G)
  simp only [E, CollectionSyntax.core, Formula.Realize, DefinableMinimaChoice.realize_rename,
    entryWitness_semantics (M := M), CollectionSyntax.firstIndex, CollectionSyntax.secondIndex,
    Fin.lastCases_last, Fin.lastCases_castSucc] at hc
  obtain ⟨family, hFamily⟩ := hc sigma hWitness
  have hSep := (GodelDefOutput.separation_semantics E (good (0 : Fin 2) 1)).mp
    ((Translation.realizes_sentence M _).mp
      ((SeparationSyntax.source_separation (good (0 : Fin 2) 1)).semantically_entails M hM))
  obtain ⟨filtered, hFiltered⟩ := hSep (fun _ => G) family
  have hf : ∀ part, E part filtered ↔ E part family ∧ Good G part := by
    intro part
    apply (hFiltered part).trans
    apply and_congr Iff.rfl
    have hr := good_semantics (M := M) (Fin.lastCases part (fun _ : Fin 1 => G)) (0 : Fin 2) (1 : Fin 2)
    have h0 : Fin.lastCases part (fun _ : Fin 1 => G) (0 : Fin 2) = G := Fin.lastCases_castSucc (0 : Fin 1)
    have h1 : Fin.lastCases part (fun _ : Fin 1 => G) (1 : Fin 2) = part := Fin.lastCases_last
    rw [h0, h1] at hr
    exact hr
  obtain ⟨g, hg⟩ := SetTheory.KP.exists_union hKP filtered
  refine ⟨g, union_good hM (fun part hp => ((hf part).mp hp).2) hg, ?_⟩
  intro tau condition he
  obtain ⟨z, hCode, hz⟩ := he
  obtain ⟨part, hPart, hGood, hValues⟩ := hFamily z hz
  obtain ⟨value, hValue⟩ := hValues tau condition hCode
  exact ⟨value, (union_edge hg tau value).mpr ⟨part, (hf part).mpr ⟨hPart, hGood⟩, hValue⟩⟩

/-- Existing Union and Separation form the precise range of active child values. -/
theorem equation_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (G g sigma : M.Carrier .set) : ∃ value, Equation G g sigma value := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hKP := SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨U, hU⟩ := SetTheory.KP.exists_union hKP g
  obtain ⟨V, hV⟩ := SetTheory.KP.exists_union hKP U
  have hBound : ∀ tau x, PureKuratowski.PairMember M tau x g → E x V := by
    intro tau x he
    obtain ⟨code, hPairCode, hMem⟩ := he
    obtain ⟨single, pair, _, hPair, hCode⟩ := hPairCode
    exact (hV x).mpr ⟨pair, (hU pair).mpr ⟨code, hMem, (hCode pair).mpr (Or.inr rfl)⟩,
      (hPair x).mpr (Or.inr rfl)⟩
  let params : Fin 3 → M.Carrier .set := Fin.cases G (Fin.cases g (fun _ => sigma))
  have hSep := (GodelDefOutput.separation_semantics E (activeValue (0 : Fin 4) 1 2 3)).mp
    ((Translation.realizes_sentence M _).mp
      ((SeparationSyntax.source_separation (activeValue (0 : Fin 4) 1 2 3)).semantically_entails M hM))
  obtain ⟨value, hValue⟩ := hSep params V
  have hs : ∀ x, Formula.Realize E (Fin.lastCases x params) (activeValue 0 1 2 3) ↔
      ∃ tau condition, PureKuratowski.PairMember M tau condition sigma ∧
        E condition G ∧ PureKuratowski.PairMember M tau x g := by
    intro x
    have hr := activeValue_semantics (M := M) (Fin.lastCases x params) (0 : Fin 4) 1 2 3
    have h0 : Fin.lastCases x params (0 : Fin 4) = G :=
      (Fin.lastCases_castSucc (0 : Fin 3)).trans Fin.cases_zero
    have h1 : Fin.lastCases x params (1 : Fin 4) = g :=
      (Fin.lastCases_castSucc (1 : Fin 3)).trans ((Fin.cases_succ (0 : Fin 2)).trans Fin.cases_zero)
    have h2 : Fin.lastCases x params (2 : Fin 4) = sigma :=
      (Fin.lastCases_castSucc (2 : Fin 3)).trans
        ((Fin.cases_succ (1 : Fin 2)).trans (Fin.cases_succ (0 : Fin 1)))
    have h3 : Fin.lastCases x params (3 : Fin 4) = x := Fin.lastCases_last
    rw [h0, h1, h2, h3] at hr
    exact hr
  refine ⟨value, fun x => ?_⟩
  constructor
  · intro hx
    exact (hs x).mp ((hValue x).mp hx).2
  · intro hx
    obtain ⟨tau, condition, he, hCondition, hEval⟩ := hx
    exact (hValue x).mpr ⟨hBound tau x hEval, (hs x).mpr ⟨tau, condition, he, hCondition, hEval⟩⟩

theorem insert_edge {g code extended sigma value : M.Carrier .set}
    (hCode : PureKuratowski.Code M code sigma value)
    (hInsert : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x extended ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x g ∨ x = code)
    (tau output : M.Carrier .set) :
    PureKuratowski.PairMember M tau output extended ↔
      PureKuratowski.PairMember M tau output g ∨ (tau = sigma ∧ output = value) := by
  constructor
  · rintro ⟨pair, hPair, hMem⟩
    rcases (hInsert pair).mp hMem with hOld | rfl
    · exact Or.inl ⟨pair, hPair, hOld⟩
    · exact Or.inr (PureKuratowski.code_injective hPair hCode)
  · intro he
    rcases he with ⟨pair, hPair, hMem⟩ | ⟨rfl, rfl⟩
    · exact ⟨pair, hPair, (hInsert pair).mpr (Or.inl hMem)⟩
    · exact ⟨code, hCode, (hInsert code).mpr (Or.inr rfl)⟩

/-- Extend a partial graph by the source range equation, preserving earlier values. -/
theorem extend_good (hM : FirstOrder.Theory.Models M nativeZF)
    {G g sigma value extended : M.Carrier .set}
    (hg : Good G g) (hCover : Covered g sigma) (hValue : Equation G g sigma value)
    (hExtended : ∀ tau output, PureKuratowski.PairMember M tau output extended ↔
      PureKuratowski.PairMember M tau output g ∨ (tau = sigma ∧ output = value)) :
    Good G extended := by
  have hAgree : ∀ x, PureKuratowski.PairMember M sigma x g → x = value := by
    intro x hx
    exact (ModelTransfer.extensionality hM).eq_of_same_members x value
      (fun z => ((hg sigma x hx).2 z).trans (hValue z).symm)
  have transfer : ∀ parent output, Covered g parent → Equation G g parent output →
      Covered extended parent ∧ Equation G extended parent output := by
    intro parent output hc heq
    constructor
    · intro tau condition he
      obtain ⟨x, hx⟩ := hc tau condition he
      exact ⟨x, (hExtended tau x).mpr (Or.inl hx)⟩
    · intro z
      constructor
      · intro hz
        obtain ⟨tau, condition, he, hCondition, hEval⟩ := (heq z).mp hz
        exact ⟨tau, condition, he, hCondition, (hExtended tau z).mpr (Or.inl hEval)⟩
      · rintro ⟨tau, condition, he, hCondition, hEval⟩
        apply (heq z).mpr
        refine ⟨tau, condition, he, hCondition, ?_⟩
        rcases (hExtended tau z).mp hEval with hOld | ⟨hTau, hZ⟩
        · exact hOld
        · subst tau
          subst z
          obtain ⟨x, hx⟩ := hc sigma condition he
          exact hAgree x hx ▸ hx
  intro parent output he
  rcases (hExtended parent output).mp he with hOld | ⟨hParent, hOutput⟩
  · exact transfer parent output (hg parent output hOld).1 (hg parent output hOld).2
  · subst parent
    subst output
    exact transfer sigma value hCover hValue

theorem existence_step (hM : FirstOrder.Theory.Models M nativeZF) (G sigma : M.Carrier .set)
    (ih : ∀ tau condition, PureKuratowski.PairMember M tau condition sigma →
      ∃ value, Evaluation G tau value) : ∃ value, Evaluation G sigma value := by
  obtain ⟨g, hg, hCover⟩ := collect_children hM G sigma ih
  obtain ⟨value, hValue⟩ := equation_exists hM G g sigma
  obtain ⟨code, hCode⟩ := KuratowskiZF.exists_code hM sigma value
  obtain ⟨extended, hInsert⟩ := SetTheory.KP.exists_insert
    (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) g code
  have he := insert_edge hCode hInsert
  exact ⟨value, extended, extend_good hM hg hCover hValue he,
    (he sigma value).mpr (Or.inr ⟨rfl, rfl⟩)⟩

def hasValue {m : Nat} (G sigma : Fin m) : Formula m :=
  .ex (evaluation G.castSucc sigma.castSucc (Fin.last m))

theorem hasValue_semantics {m : Nat} (v : Fin m → M.Carrier .set) (G sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (hasValue G sigma) ↔
      ∃ value, Evaluation (v G) (v sigma) value := by
  simp only [hasValue, Formula.Realize, evaluation_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF) (G sigma : M.Carrier .set) :
    ∃ value, Evaluation G sigma value := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  let p := hasValue (0 : Fin 2) 1
  let v : Fin 1 → M.Carrier .set := fun _ => G
  have hp : ∀ tau, Formula.Realize E (Fin.lastCases tau v) p ↔ ∃ value, Evaluation G tau value := by
    intro tau
    have hr := hasValue_semantics (M := M) (Fin.lastCases tau v) (0 : Fin 2) 1
    have h0 : Fin.lastCases tau v (0 : Fin 2) = G := Fin.lastCases_castSucc (0 : Fin 1)
    have h1 : Fin.lastCases tau v (1 : Fin 2) = tau := Fin.lastCases_last
    rw [h0, h1] at hr
    exact hr
  have hi := (GodelDefOutput.close_semantics E _).mp
    ((Translation.realizes_sentence M _).mp
      ((ForcingNameInduction.kernel_certificate p).semantically_entails M hM)) v
  change Formula.Realize E v (ForcingNameInduction.progressive p id) →
    Formula.Realize E v (SetInductionSyntax.holds p id) at hi
  have hAll := hi ((ForcingNameInduction.progressive_semantics v p id).mpr (by
    intro tau ih
    apply (hp tau).mpr
    apply existence_step hM G tau
    intro child condition he
    exact (hp child).mp (ih child ⟨condition, he⟩)))
  exact (hp sigma).mp ((ForcingNameInduction.holds_semantics E v p id).mp hAll sigma)

/-- The original mem_evaluate_iff, now with the internal evaluation relation. -/
theorem mem_evaluation (hM : FirstOrder.Theory.Models M nativeZF)
    {G sigma value : M.Carrier .set} (h : Evaluation G sigma value) (x : M.Carrier .set) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem x value ↔
      ∃ tau condition, PureKuratowski.PairMember M tau condition sigma ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition G ∧ Evaluation G tau x := by
  obtain ⟨g, hg, hValue⟩ := h
  obtain ⟨hc, heq⟩ := hg sigma value hValue
  constructor
  · intro hx
    obtain ⟨tau, condition, he, hCondition, hEval⟩ := (heq x).mp hx
    exact ⟨tau, condition, he, hCondition, g, hg, hEval⟩
  · rintro ⟨tau, condition, he, hCondition, hEval⟩
    obtain ⟨y, hy⟩ := hc tau condition he
    have heq' := unique hM hEval ⟨g, hg, hy⟩
    exact (heq x).mpr ⟨tau, condition, he, hCondition, heq'.symm ▸ hy⟩

def existenceSentence : Source.Sentence := (hasValue (0 : Fin 2) 1).close

def uniquenessSentence : Source.Sentence :=
  ((evaluation (0 : Fin 4) 1 2).imp ((evaluation 0 1 3).imp (.equal 2 3))).close

def unfoldingSentence : Source.Sentence :=
  ((evaluation (0 : Fin 4) 1 2).imp ((Formula.mem 3 2).iff
    (.ex (.ex ((Source.SetLanguage.edge (1 : Fin 6) 4 5).conj
      ((Formula.mem 5 0).conj (evaluation 0 4 3))))))).close

theorem existence_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence existenceSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  exact (hasValue_semantics v 0 1).mpr (exists_value hM (v 0) (v 1))

theorem uniqueness_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence uniquenessSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hx hy
  exact unique hM ((evaluation_semantics v 0 1 2).mp hx) ((evaluation_semantics v 0 1 3).mp hy)

theorem unfolding_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence unfoldingSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  have he := mem_evaluation hM ((evaluation_semantics v 0 1 2).mp h) (v 3)
  change (_ → Formula.Realize _ v _) ∧ (Formula.Realize _ v _ → _)
  have hr : Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v
      (.ex (.ex ((Source.SetLanguage.edge (1 : Fin 6) 4 5).conj
        ((Formula.mem 5 0).conj (evaluation 0 4 3))))) ↔
      ∃ tau condition, PureKuratowski.PairMember M tau condition (v 1) ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition (v 0) ∧ Evaluation (v 0) tau (v 3) := by
    simp only [Formula.Realize, KuratowskiZF.source_edge, evaluation_semantics (M := M)]
    rfl
  exact ⟨fun hx => hr.mpr (he.mp hx), fun hx => he.mpr (hr.mp hx)⟩

theorem existence_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  ModelTransfer.derives (fun _ hM => existence_models hM)

theorem uniqueness_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence uniquenessSentence) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models hM)

theorem unfolding_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence unfoldingSentence) :=
  ModelTransfer.derives (fun _ hM => unfolding_models hM)

theorem empty_evaluation (hM : FirstOrder.Theory.Models M nativeZF)
    (G empty : M.Carrier .set)
    (hEmpty : ∀ x, ¬ (Definitional.Project.FirstOrderSemantics.reduct M).mem x empty) :
    Evaluation G empty empty := by
  obtain ⟨value, hValue⟩ := exists_value hM G empty
  have heq : value = empty := by
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro x
    constructor
    · intro hx
      obtain ⟨tau, condition, he, _, _⟩ := (mem_evaluation hM hValue x).mp hx
      obtain ⟨code, _, hc⟩ := he
      exact False.elim (hEmpty code hc)
    · intro hx
      exact False.elim (hEmpty x hx)
  exact heq ▸ hValue

def emptySentence : Source.Sentence :=
  ((Formula.all ((Formula.mem (Fin.last 2) (1 : Fin 2).castSucc).neg)).imp
    (evaluation (0 : Fin 2) 1 1)).close

theorem empty_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence emptySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  exact (evaluation_semantics v 0 1 1).mpr (empty_evaluation hM (v 0) (v 1) h)

theorem empty_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence emptySentence) :=
  ModelTransfer.derives (fun _ hM => empty_models hM)

end PPAC.Migration.ForcingEvaluation
