/- Exact existing Gödel-definability output formula, now with original-ZF
existence and uniqueness certificates for all fourteen internal parameters.
The predicate is translated from the pinned existing syntax slice. Its
existence uses Power Set and full Separation; uniqueness uses Extensionality.
No evaluator correctness, external well-foundedness or Choice premise is used.
This is the Def-step construction, not the full constructible interpretation. -/
import PPAC.Migration.ExistingConstructibleSyntax
import PPAC.Migration.KuratowskiZF
import PPAC.Migration.SeparationSyntax

namespace PPAC.Migration.GodelDefOutput
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open ExistingConstructible
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
universe u
variable {A : Type u}

def toSource {n : Nat} : Constructible.FOFormula n → Source.Formula n
  | .mem i j => .mem i j
  | .eq i j => .equal i j
  | .neg p => (toSource p).neg
  | .conj p q => (toSource p).conj (toSource q)
  | .ex p => .ex (toSource p)

theorem toSource_rename {n m : Nat} (p : Constructible.FOFormula n) (r : Fin n → Fin m) :
    toSource (Constructible.FOFormula.rename r p) = (toSource p).rename r := by
  induction p generalizing m with
  | mem | eq => rfl
  | neg p ih => simp only [Constructible.FOFormula.rename, toSource, Source.Formula.rename, ih]
  | conj p q hp hq => simp only [Constructible.FOFormula.rename, toSource, Source.Formula.rename, hp, hq]
  | ex p ih =>
      simp only [Constructible.FOFormula.rename, toSource, Source.Formula.rename, ih]
      rfl

theorem all_semantics (E : A → A → Prop) {n : Nat} (p : Constructible.FOFormula (n+1))
    (v : Fin n → A) :
    Source.Formula.Realize E v (toSource (Constructible.FOFormula.all p)) ↔
      ∀ x, Source.Formula.Realize E (Fin.lastCases x v) (toSource p) := by
  classical
  simp only [Constructible.FOFormula.all, toSource, Source.Formula.Realize]
  constructor
  · intro h x
    exact Classical.byContradiction (fun hn => h ⟨x, hn⟩)
  · rintro h ⟨x, hn⟩
    exact hn (h x)

theorem imp_semantics (E : A → A → Prop) {n : Nat} (p q : Constructible.FOFormula n)
    (v : Fin n → A) :
    Source.Formula.Realize E v (toSource (Constructible.FOFormula.imp p q)) ↔
      (Source.Formula.Realize E v (toSource p) → Source.Formula.Realize E v (toSource q)) := by
  classical
  simp only [Constructible.FOFormula.imp, Constructible.FOFormula.disj,
    toSource, Source.Formula.Realize]
  constructor
  · intro h hp
    exact Classical.byContradiction (fun hn => h ⟨(fun hnp => hnp hp), hn⟩)
  · rintro h ⟨hnnp, hnq⟩
    exact hnnp (fun hp => hnq (h hp))

theorem iff_semantics (E : A → A → Prop) {n : Nat} (p q : Constructible.FOFormula n)
    (v : Fin n → A) :
    Source.Formula.Realize E v (toSource (Constructible.FOFormula.biimp p q)) ↔
      (Source.Formula.Realize E v (toSource p) ↔ Source.Formula.Realize E v (toSource q)) := by
  change (Source.Formula.Realize E v (toSource (Constructible.FOFormula.imp p q)) ∧
    Source.Formula.Realize E v (toSource (Constructible.FOFormula.imp q p))) ↔ _
  rw [imp_semantics, imp_semantics]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩

theorem subset_semantics (E : A → A → Prop) {n : Nat} (x y : Fin n) (v : Fin n → A) :
    Source.Formula.Realize E v (toSource ((Constructible.Delta0Formula.subsetAt x y).toFO)) ↔
      ∀ z, E z (v x) → E z (v y) := by
  classical
  simp only [Constructible.Delta0Formula.subsetAt, Constructible.Delta0Formula.boundedAll,
    Constructible.Delta0Formula.toFO, Constructible.FOFormula.boundedEx,
    toSource, Source.Formula.Realize, Fin.lastCases_last, Fin.lastCases_castSucc]
  constructor
  · intro h z hz
    exact Classical.byContradiction (fun hn => h ⟨z, hz, hn⟩)
  · rintro h ⟨z, hz, hn⟩
    exact hn (h z hz)

def evaluator : Source.Formula 16 :=
  toSource Constructible.Godel.RudimentaryTerm.stackProgramEvalFormula

def output : Source.Formula 15 :=
  toSource Constructible.Godel.RudimentaryTerm.godelDefOutputFormula

attribute [local irreducible] Constructible.Godel.RudimentaryTerm.stackProgramEvalFormula

theorem output_semantics (E : A → A → Prop) (params : Fin 14 → A) (d : A) :
    Source.Formula.Realize E (Fin.lastCases d params) output ↔
      ∀ x, E x d ↔ (∀ z, E z x → E z (params 0)) ∧
        ∃ code, Source.Formula.Realize E (Fin.lastCases x (Fin.lastCases code params)) evaluator := by
  unfold output
  rw [Constructible.Godel.RudimentaryTerm.godelDefOutputFormula, all_semantics]
  apply forall_congr'
  intro x
  rw [iff_semantics]
  change (E x d ↔
    Source.Formula.Realize E (Fin.lastCases x (Fin.lastCases d params))
      (toSource ((Constructible.Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO)) ∧
    ∃ code, Source.Formula.Realize E (Fin.lastCases code (Fin.lastCases x (Fin.lastCases d params)))
      (toSource (Constructible.FOFormula.rename Constructible.Godel.RudimentaryTerm.godelDefEvalRename
        Constructible.Godel.RudimentaryTerm.stackProgramEvalFormula))) ↔ _
  rw [subset_semantics]
  simp only [toSource_rename, DefinableMinimaChoice.realize_rename]
  have he (code : A) :
      (fun i => Fin.lastCases code (Fin.lastCases x (Fin.lastCases d params))
        (Constructible.Godel.RudimentaryTerm.godelDefEvalRename i)) =
      Fin.lastCases x (Fin.lastCases code params) := by
    funext i
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => ?_) j) i
    · rfl
    · rfl
    · simp only [Constructible.Godel.RudimentaryTerm.godelDefEvalRename,
        Fin.lastCases_castSucc]
  have hp : ((∀ z, E z x → E z (params 0)) ∧ ∃ code,
      Source.Formula.Realize E
        (fun i => Fin.lastCases code (Fin.lastCases x (Fin.lastCases d params))
          (Constructible.Godel.RudimentaryTerm.godelDefEvalRename i))
        (toSource Constructible.Godel.RudimentaryTerm.stackProgramEvalFormula)) ↔
      ((∀ z, E z x → E z (params 0)) ∧ ∃ code,
        Source.Formula.Realize E (Fin.lastCases x (Fin.lastCases code params)) evaluator) := by
    apply and_congr Iff.rfl
    apply exists_congr
    intro code
    rw [he]
    exact Iff.rfl
  exact ⟨fun h => h.trans hp, fun h => h.trans hp.symm⟩

def query : Source.Formula 15 := .ex (evaluator.rename
  (Fin.lastCases (14 : Fin 16) (Fin.lastCases (15 : Fin 16)
    (fun i : Fin 14 => i.castSucc.castSucc))))

theorem query_semantics (E : A → A → Prop) (params : Fin 14 → A) (x : A) :
    Source.Formula.Realize E (Fin.lastCases x params) query ↔
      ∃ code, Source.Formula.Realize E (Fin.lastCases x (Fin.lastCases code params)) evaluator := by
  simp only [query, Source.Formula.Realize, DefinableMinimaChoice.realize_rename]
  apply exists_congr
  intro code
  have he : (fun i => Fin.lastCases code (Fin.lastCases x params)
      (Fin.lastCases (14 : Fin 16) (Fin.lastCases (15 : Fin 16)
        (fun j : Fin 14 => j.castSucc.castSucc)) i)) =
      Fin.lastCases x (Fin.lastCases code params) := by
    funext i
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => ?_) j) i
    · rfl
    · rfl
    · simp only [Fin.lastCases_castSucc]
  rw [he]

theorem close_semantics (E : A → A → Prop) {n : Nat} (p : Source.Formula n) :
    Source.Formula.Realize E Fin.elim0 p.close ↔
      ∀ v : Fin n → A, Source.Formula.Realize E v p := by
  induction n with
  | zero =>
    constructor
    · intro h v
      have he : v = Fin.elim0 := by funext i; exact Fin.elim0 i
      simpa only [he, Source.Formula.close] using h
    · intro h
      exact h Fin.elim0
  | succ n ih =>
    change Source.Formula.Realize E Fin.elim0 (Source.Formula.all p).close ↔ _
    rw [ih]
    change (∀ v x, Source.Formula.Realize E (Fin.lastCases x v) p) ↔ _
    constructor
    · intro h v
      have he : Fin.lastCases (v (Fin.last n)) (fun i => v i.castSucc) = v := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;>
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      simpa only [he] using h (fun i => v i.castSucc) (v (Fin.last n))
    · intro h v x
      exact h (Fin.lastCases x v)

theorem separation_semantics (E : A → A → Prop) {n : Nat} (p : Source.Formula (n+1)) :
    Source.Formula.Realize E Fin.elim0 (Source.SetLanguage.separation p) ↔
      ∀ params : Fin n → A, ∀ a, ∃ b, ∀ x,
        E x b ↔ E x a ∧ Source.Formula.Realize E (Fin.lastCases x params) p := by
  simp only [Source.SetLanguage.separation, close_semantics]
  apply forall_congr'
  intro params
  simp only [Source.Formula.Realize, DefinableMinimaChoice.realize_rename]
  apply forall_congr'
  intro a
  apply exists_congr
  intro b
  apply forall_congr'
  intro x
  have he : (fun i => Fin.lastCases x (Fin.lastCases b (Fin.lastCases a params))
      (SeparationSyntax.matrixIndex i)) = Fin.lastCases x params := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [SeparationSyntax.matrixIndex, Fin.lastCases_last, Fin.lastCases_castSucc]
  simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  change ((E x b → E x a ∧ Source.Formula.Realize E
    (fun i => Fin.lastCases x (Fin.lastCases b (Fin.lastCases a params))
      (SeparationSyntax.matrixIndex i)) p) ∧
    ((E x a ∧ Source.Formula.Realize E
    (fun i => Fin.lastCases x (Fin.lastCases b (Fin.lastCases a params))
      (SeparationSyntax.matrixIndex i)) p) → E x b)) ↔ _
  rw [he]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩

theorem exists_unique {M : FirstOrder.Structure.{0,0,0,u} ℒ}
    (hM : FirstOrder.Theory.Models M nativeZF) (params : Fin 14 → M.Carrier .set) :
    ∃ d, Source.Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases d params) output ∧
      ∀ other, Source.Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
        (Fin.lastCases other params) output → other = d := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨power, hPower⟩ := SetTheory.ZF.exists_powerSet hZF (params 0)
  have hSep := (separation_semantics E query).mp
    ((Translation.realizes_sentence M _).mp
      ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨d, hd⟩ := hSep params power
  have hOut : Source.Formula.Realize E (Fin.lastCases d params) output := by
    apply (output_semantics E params d).mpr
    intro x
    exact (hd x).trans (and_congr (hPower x) (query_semantics E params x))
  refine ⟨d, hOut, ?_⟩
  intro other hOther
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  intro x
  exact ((output_semantics E params other).mp hOther x).trans
    ((output_semantics E params d).mp hOut x).symm

def existenceSentence : Source.Sentence := (Source.Formula.ex output).close

def otherIndex : Fin 15 → Fin 16 :=
  Fin.lastCases (Fin.last 15) (fun i : Fin 14 => i.castSucc.castSucc)

def uniquenessSentence : Source.Sentence :=
  (output.raise.imp ((output.rename otherIndex).imp
    (Source.Formula.equal (14 : Fin 16) 15))).close

theorem existence_models {M : FirstOrder.Structure.{0,0,0,u} ℒ}
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence existenceSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (close_semantics _ (Source.Formula.ex output)).mpr
  intro params
  obtain ⟨d, hd, _⟩ := exists_unique hM params
  exact ⟨d, hd⟩

theorem uniqueness_models {M : FirstOrder.Structure.{0,0,0,u} ℒ}
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence uniquenessSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (close_semantics _ _).mpr
  intro v
  simp only [Source.Formula.Realize, Source.Formula.raise, DefinableMinimaChoice.realize_rename]
  intro hFirst hSecond
  let params : Fin 14 → M.Carrier .set := fun i => v i.castSucc.castSucc
  let d := v (Fin.last 14).castSucc
  let e := v (Fin.last 15)
  have h₁ : (fun i : Fin 15 => v i.castSucc) = Fin.lastCases d params := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
    · rfl
    · rfl
  have h₂ : (fun i => v (otherIndex i)) = Fin.lastCases e params := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [otherIndex, Fin.lastCases_last, Fin.lastCases_castSucc]
    · rfl
    · rfl
  rw [h₁] at hFirst
  rw [h₂] at hSecond
  obtain ⟨w, _, hUnique⟩ := exists_unique hM params
  exact (hUnique d hFirst).trans (hUnique e hSecond).symm

theorem existence_kernel_certificate : FirstOrder.Derives nativeZF []
    (Translation.sentence existenceSentence) :=
  ModelTransfer.derives (fun _ hM => existence_models hM)

theorem uniqueness_kernel_certificate : FirstOrder.Derives nativeZF []
    (Translation.sentence uniquenessSentence) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models hM)

theorem source_existence_certificate : Source.Derives (Source.SetLanguage.ZF.at 1)
    (existenceSentence.rename Fin.elim0) :=
  ReverseZFReplay.source_sentence existence_kernel_certificate

theorem source_uniqueness_certificate : Source.Derives (Source.SetLanguage.ZF.at 1)
    (uniquenessSentence.rename Fin.elim0) :=
  ReverseZFReplay.source_sentence uniqueness_kernel_certificate

end PPAC.Migration.GodelDefOutput
