/- Object adaptation of the pinned OpenAI Forcing/ForcingNames.lean,
IsName, isName_iff, IsName.intro/edges/child/condition and isName_empty.
The recursive predicate is represented by an internal closed-set witness.
Collection and Separation assemble witnesses without choosing a family.
All conclusions are returned to the original nativeZF derivation kernel.
This does not implement evaluate, mapConditions or atomic forcing. -/
import PPAC.Migration.ForcingNameInduction
import PPAC.Migration.CollectionSyntax

namespace PPAC.Migration.ForcingNames
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Every entry has the original ordered-pair shape, with a child in S. -/
def entry {m : Nat} (P z S : Fin m) : Formula m :=
  .ex (.ex ((PairSyntax.ordered z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
      (.mem (Fin.last m).castSucc S.castSucc.castSucc))))

def closed {m : Nat} (P S : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) S.castSucc).imp
    (.all ((Formula.mem (Fin.last (m+1)) (Fin.last m).castSucc).imp
      (entry P.castSucc.castSucc (Fin.last (m+1)) S.castSucc.castSucc))))

def isName {m : Nat} (P sigma : Fin m) : Formula m :=
  .ex ((Formula.mem sigma.castSucc (Fin.last m)).conj (closed P.castSucc (Fin.last m)))

def nameEntry {m : Nat} (P z : Fin m) : Formula m :=
  .ex (.ex ((PairSyntax.ordered z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
      (isName P.castSucc.castSucc (Fin.last m).castSucc))))

def step {m : Nat} (P sigma : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) sigma.castSucc).imp (nameEntry P.castSucc (Fin.last m)))

/-- Literal two-conjunct equation in the original isName_iff. -/
def originalStep {m : Nat} (P sigma : Fin m) : Formula m :=
  (Formula.all ((Formula.mem (Fin.last m) sigma.castSucc).imp
    (.ex (.ex (PairSyntax.ordered (Fin.last m).castSucc.castSucc
      (Fin.last (m+1)).castSucc (Fin.last (m+2))))))).conj
    (.all (.all ((Source.SetLanguage.edge sigma.castSucc.castSucc
      (Fin.last m).castSucc (Fin.last (m+1))).imp
        ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
          (isName P.castSucc.castSucc (Fin.last m).castSucc)))))

def witness : Formula 3 := (closed 0 2).conj (entry 0 1 2)

def Closed (P S : M.Carrier .set) : Prop :=
  ∀ rho, (Definitional.Project.FirstOrderSemantics.reduct M).mem rho S →
    ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z rho →
      ∃ tau condition, PureKuratowski.Code M z tau condition ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition P ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem tau S

def IsName (P sigma : M.Carrier .set) : Prop :=
  ∃ S, (Definitional.Project.FirstOrderSemantics.reduct M).mem sigma S ∧ Closed P S

theorem entry_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P z S : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (entry P z S) ↔
      ∃ tau condition, PureKuratowski.Code M (v z) tau condition ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition (v P) ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem tau (v S) := by
  simp only [entry, Formula.Realize, KuratowskiZF.source_code,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem closed_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P S : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (closed P S) ↔
      Closed (v P) (v S) := by
  simp only [closed, Formula.Realize, entry_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc, Closed]

theorem isName_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (isName P sigma) ↔
      IsName (v P) (v sigma) := by
  simp only [isName, Formula.Realize, closed_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc, IsName]

theorem nameEntry_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P z : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (nameEntry P z) ↔
      ∃ tau condition, PureKuratowski.Code M (v z) tau condition ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition (v P) ∧
        IsName (v P) tau := by
  simp only [nameEntry, Formula.Realize, KuratowskiZF.source_code, isName_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem step_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (step P sigma) ↔
      ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z (v sigma) →
        ∃ tau condition, PureKuratowski.Code M z tau condition ∧
          (Definitional.Project.FirstOrderSemantics.reduct M).mem condition (v P) ∧
          IsName (v P) tau := by
  simp only [step, Formula.Realize, nameEntry_semantics,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem originalStep_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (originalStep P sigma) ↔
      (∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z (v sigma) →
        ∃ tau condition, PureKuratowski.Code M z tau condition) ∧
      (∀ tau condition, PureKuratowski.PairMember M tau condition (v sigma) →
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition (v P) ∧ IsName (v P) tau) := by
  simp only [originalStep, Formula.Realize, KuratowskiZF.source_code,
    KuratowskiZF.source_edge, isName_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem edges {P sigma : M.Carrier .set} (h : IsName P sigma) :
    ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z sigma →
      ∃ tau condition, PureKuratowski.Code M z tau condition ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition P ∧ IsName P tau := by
  obtain ⟨S, hSigma, hClosed⟩ := h
  intro z hz
  obtain ⟨tau, condition, hCode, hCondition, hTau⟩ := hClosed sigma hSigma z hz
  exact ⟨tau, condition, hCode, hCondition, S, hTau, hClosed⟩

theorem child_condition {P sigma tau condition : M.Carrier .set} (h : IsName P sigma)
    (he : PureKuratowski.PairMember M tau condition sigma) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem condition P ∧ IsName P tau := by
  obtain ⟨z, hCode, hz⟩ := he
  obtain ⟨tau', condition', hCode', hCondition, hTau⟩ := edges h z hz
  obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hCode hCode'
  exact ⟨hCondition, hTau⟩

/-- Full native Collection at the one exact witness matrix required by IsName.intro. -/
theorem collect_witnesses (hM : FirstOrder.Theory.Models M nativeZF)
    (P sigma : M.Carrier .set)
    (h : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z sigma →
      ∃ S, Closed P S ∧ ∃ tau condition, PureKuratowski.Code M z tau condition ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition P ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem tau S) :
    ∃ family, ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z sigma →
      ∃ S, (Definitional.Project.FirstOrderSemantics.reduct M).mem S family ∧
        Closed P S ∧ ∃ tau condition, PureKuratowski.Code M z tau condition ∧
          (Definitional.Project.FirstOrderSemantics.reduct M).mem condition P ∧
          (Definitional.Project.FirstOrderSemantics.reduct M).mem tau S := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hc := (GodelDefOutput.close_semantics E (CollectionSyntax.core witness)).mp
    ((Translation.realizes_sentence M _).mp
      ((CollectionSyntax.source_collection witness).semantically_entails M hM)) (fun _ => P)
  simp only [E, CollectionSyntax.core, Formula.Realize, DefinableMinimaChoice.realize_rename,
    witness, closed_semantics (M := M), entry_semantics (M := M), CollectionSyntax.firstIndex,
    CollectionSyntax.secondIndex, Fin.lastCases_last, Fin.lastCases_castSucc] at hc
  exact hc sigma h

/-- Collection may contain junk; separate closed witnesses before taking their union. -/
theorem intro_name (hM : FirstOrder.Theory.Models M nativeZF) (P sigma : M.Carrier .set)
    (h : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z sigma →
      ∃ tau condition, PureKuratowski.Code M z tau condition ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition P ∧ IsName P tau) :
    IsName P sigma := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hKP := SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨family, hFamily⟩ := collect_witnesses hM P sigma (by
    intro z hz
    obtain ⟨tau, condition, hCode, hCondition, S, hTau, hClosed⟩ := h z hz
    exact ⟨S, hClosed, tau, condition, hCode, hCondition, hTau⟩)
  have hSep := (GodelDefOutput.separation_semantics E (closed (0 : Fin 2) 1)).mp
    ((Translation.realizes_sentence M _).mp
      ((SeparationSyntax.source_separation (closed (0 : Fin 2) 1)).semantically_entails M hM))
  obtain ⟨good, hGood⟩ := hSep (fun _ => P) family
  have hGood' : ∀ S, E S good ↔ E S family ∧ Closed P S := by
    intro S
    apply (hGood S).trans
    apply and_congr Iff.rfl
    have hc := closed_semantics (M := M) (Fin.lastCases S (fun _ : Fin 1 => P))
      (0 : Fin 2) (1 : Fin 2)
    change Formula.Realize E (Fin.lastCases S (fun _ : Fin 1 => P)) (closed 0 1) ↔ _ at hc
    have h0 : Fin.lastCases S (fun _ : Fin 1 => P) (0 : Fin 2) = P := by
      exact Fin.lastCases_castSucc (0 : Fin 1)
    have h1 : Fin.lastCases S (fun _ : Fin 1 => P) (1 : Fin 2) = S := by
      exact Fin.lastCases_last
    rw [h0, h1] at hc
    exact hc
  obtain ⟨U, hU⟩ := SetTheory.KP.exists_union hKP good
  obtain ⟨S, hS⟩ := SetTheory.KP.exists_insert hKP U sigma
  refine ⟨S, (hS sigma).mpr (Or.inr rfl), ?_⟩
  intro rho hRho z hz
  rcases (hS rho).mp hRho with hInU | rfl
  · obtain ⟨part, hPart, hRhoPart⟩ := (hU rho).mp hInU
    obtain ⟨tau, condition, hCode, hCondition, hTau⟩ :=
      ((hGood' part).mp hPart).2 rho hRhoPart z hz
    exact ⟨tau, condition, hCode, hCondition,
      (hS tau).mpr (Or.inl ((hU tau).mpr ⟨part, hPart, hTau⟩))⟩
  · obtain ⟨part, hPart, hClosed, tau, condition, hCode, hCondition, hTau⟩ := hFamily z hz
    exact ⟨tau, condition, hCode, hCondition,
      (hS tau).mpr (Or.inl ((hU tau).mpr ⟨part, (hGood' part).mpr ⟨hPart, hClosed⟩, hTau⟩))⟩

theorem empty_name (hM : FirstOrder.Theory.Models M nativeZF) (P empty : M.Carrier .set)
    (hEmpty : ∀ x, ¬ (Definitional.Project.FirstOrderSemantics.reduct M).mem x empty) :
    IsName P empty :=
  intro_name hM P empty (fun z hz => False.elim (hEmpty z hz))

def unfoldingSentence : Source.Sentence := ((isName (0 : Fin 2) 1).iff (originalStep 0 1)).close

def edgesSentence : Source.Sentence := ((isName (0 : Fin 2) 1).iff (step 0 1)).close

def emptySentence : Source.Sentence :=
  ((Formula.all ((Formula.mem (Fin.last 2) (1 : Fin 2).castSucc).neg)).imp
    (isName (0 : Fin 2) 1)).close

theorem unfolding_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence unfoldingSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  change (Formula.Realize _ v (isName 0 1) → Formula.Realize _ v (originalStep 0 1)) ∧
    (Formula.Realize _ v (originalStep 0 1) → Formula.Realize _ v (isName 0 1))
  constructor
  · intro h
    have hn := (isName_semantics v 0 1).mp h
    apply (originalStep_semantics v 0 1).mpr
    exact ⟨fun z hz => by
      obtain ⟨tau, condition, hCode, _, _⟩ := edges hn z hz
      exact ⟨tau, condition, hCode⟩,
      fun tau condition he => child_condition hn he⟩
  · intro h
    have hs := (originalStep_semantics v 0 1).mp h
    apply (isName_semantics v 0 1).mpr
    apply intro_name hM
    intro z hz
    obtain ⟨tau, condition, hCode⟩ := hs.1 z hz
    have ht := hs.2 tau condition ⟨z, hCode, hz⟩
    exact ⟨tau, condition, hCode, ht.1, ht.2⟩

theorem edges_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence edgesSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  change (Formula.Realize _ v (isName 0 1) → Formula.Realize _ v (step 0 1)) ∧
    (Formula.Realize _ v (step 0 1) → Formula.Realize _ v (isName 0 1))
  exact ⟨fun h => (step_semantics v 0 1).mpr (edges ((isName_semantics v 0 1).mp h)),
    fun h => (isName_semantics v 0 1).mpr (intro_name hM (v 0) (v 1)
      ((step_semantics v 0 1).mp h))⟩

theorem empty_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence emptySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  intro h
  apply (isName_semantics v 0 1).mpr
  exact empty_name hM (v 0) (v 1) h

theorem unfolding_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence unfoldingSentence) :=
  ModelTransfer.derives (fun _ hM => unfolding_models hM)

theorem edges_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence edgesSentence) :=
  ModelTransfer.derives (fun _ hM => edges_models hM)

theorem empty_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence emptySentence) :=
  ModelTransfer.derives (fun _ hM => empty_models hM)

/-- Original entry step with an arbitrary definable recursive predicate. -/
def stepWith {n m : Nat} (p : Formula (n+1)) (rho : Fin n → Fin m)
    (P sigma : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) sigma.castSucc).imp
    (.ex (.ex ((PairSyntax.ordered (Fin.last m).castSucc.castSucc
      (Fin.last (m+1)).castSucc (Fin.last (m+2))).conj
        ((Formula.mem (Fin.last (m+2)) P.castSucc.castSucc.castSucc).conj
          (MinimalPredicates.pred p (fun i => (rho i).castSucc.castSucc.castSucc)
            (Fin.last (m+1)).castSucc))))))

def equation {n : Nat} (p : Formula (n+1)) (P : Fin n) : Formula n :=
  .all (p.iff (stepWith p Fin.castSucc P.castSucc (Fin.last n)))

def comparison {n : Nat} (p : Formula (n+1)) (P : Fin n) : Formula (n+1) :=
  p.iff (isName P.castSucc (Fin.last n))

def uniquenessSentence {n : Nat} (p : Formula (n+1)) (P : Fin n) : Source.Sentence :=
  ((equation p P).imp (.all (comparison p P))).close

theorem stepWith_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (p : Formula (n+1)) (rho : Fin n → Fin m) (P sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (stepWith p rho P sigma) ↔
      ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z (v sigma) →
        ∃ tau condition, PureKuratowski.Code M z tau condition ∧
          (Definitional.Project.FirstOrderSemantics.reduct M).mem condition (v P) ∧
          Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
            (Fin.lastCases tau (fun i => v (rho i))) p := by
  simp only [stepWith, Formula.Realize, KuratowskiZF.source_code,
    ForcingNameInduction.pred_semantics, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem comparison_semantics {n : Nat} (v : Fin n → M.Carrier .set)
    (p : Formula (n+1)) (P : Fin n) (sigma : M.Carrier .set) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases sigma v) (comparison p P) ↔
      (Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
        (Fin.lastCases sigma v) p ↔ IsName (v P) sigma) := by
  simp only [comparison, Source.Formula.iff, Formula.Realize, isName_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- Child induction identifies the closed-set definition with every definable
solution of the original recursive equation, including in nonstandard models. -/
theorem uniqueness_models {n : Nat} (p : Formula (n+1)) (P : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (uniquenessSentence p P)).TrueIn M := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics E _).mpr
  intro v
  change Formula.Realize E v (equation p P) → ∀ sigma,
    Formula.Realize E (Fin.lastCases sigma v) (comparison p P)
  intro heq
  have eqAt : ∀ sigma, Formula.Realize E (Fin.lastCases sigma v) p ↔
      ∀ z, E z sigma → ∃ tau condition, PureKuratowski.Code M z tau condition ∧
        E condition (v P) ∧ Formula.Realize E (Fin.lastCases tau v) p := by
    intro sigma
    have h := heq sigma
    change (Formula.Realize E (Fin.lastCases sigma v) p →
      Formula.Realize E (Fin.lastCases sigma v) (stepWith p Fin.castSucc P.castSucc (Fin.last n))) ∧
      (Formula.Realize E (Fin.lastCases sigma v) (stepWith p Fin.castSucc P.castSucc (Fin.last n)) →
        Formula.Realize E (Fin.lastCases sigma v) p) at h
    have hs := stepWith_semantics (M := M) (Fin.lastCases sigma v) p Fin.castSucc P.castSucc (Fin.last n)
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hs
    exact ⟨fun hp => hs.mp (h.1 hp), fun hp => h.2 (hs.mpr hp)⟩
  have hi := (GodelDefOutput.close_semantics E _).mp
    ((Translation.realizes_sentence M _).mp
      ((ForcingNameInduction.kernel_certificate (comparison p P)).semantically_entails M hM)) v
  change Formula.Realize E v (ForcingNameInduction.progressive (comparison p P) id) →
    Formula.Realize E v (SetInductionSyntax.holds (comparison p P) id) at hi
  have hAll := hi ((ForcingNameInduction.progressive_semantics v (comparison p P) id).mpr (by
    intro sigma ih
    apply (comparison_semantics v p P sigma).mpr
    constructor
    · intro hp
      apply intro_name hM (v P) sigma
      intro z hz
      obtain ⟨tau, condition, hCode, hCondition, hTau⟩ := (eqAt sigma).mp hp z hz
      have ht := (comparison_semantics v p P tau).mp (ih tau ⟨condition, z, hCode, hz⟩)
      exact ⟨tau, condition, hCode, hCondition, ht.mp hTau⟩
    · intro hn
      apply (eqAt sigma).mpr
      intro z hz
      obtain ⟨tau, condition, hCode, hCondition, hTau⟩ := edges hn z hz
      have ht := (comparison_semantics v p P tau).mp (ih tau ⟨condition, z, hCode, hz⟩)
      exact ⟨tau, condition, hCode, hCondition, ht.mpr hTau⟩))
  exact (ForcingNameInduction.holds_semantics E v (comparison p P) id).mp hAll

theorem uniqueness_kernel_certificate {n : Nat} (p : Formula (n+1)) (P : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence p P)) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models p P hM)

end PPAC.Migration.ForcingNames
