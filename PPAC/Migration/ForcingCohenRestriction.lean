/- Pinned AssignedGraphs.Condition.restrictedGraph:394-400 and hcode/hd:422-433.
Restrict by membership of some(graph entry) in an arbitrary Option-value set.
Reuse native Separation, the existing condition carrier and small_subset.
This is not the earlier restriction by coordinate LABELS. -/
import PPAC.Migration.ForcingCohenCompatibleChoice

namespace PPAC.Migration.ForcingCohenRestriction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingWithTopCarrier (Empty Single Element)
open ForcingCohenConditions (Condition)
open ConstructionCohenCompatibility (Compatible)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
universe u
set_option maxRecDepth 8192
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def SomeIn (Y z : M.Carrier .set) : Prop :=
  ∃ y, Single y z ∧ (Project.FirstOrderSemantics.reduct M).mem y Y

def someIn {m} (Y z : Fin m) : Project.Formula 1 m := .existsE (.conj
  (Project.Formula.isSingleton .newest (.bound z.succ)) (.mem .newest (.bound Y.succ)))
derive_free_closed someIn

theorem someIn_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (Y z : Fin m) :
    Project.Formula.satisfies ρ (someIn Y z) ↔ SomeIn (ρ.bound Y) (ρ.bound z) := by
  simp only [someIn,SomeIn,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isSingleton_iff (ModelTransfer.extensionality hM),Project.Formula.satisfies_mem_iff]
  rfl

theorem someIn_member (hM : FirstOrder.Theory.Models M nativeZF) {Y z y : M.Carrier .set}
    (h : SomeIn Y z) (hy : Single y z) : (Project.FirstOrderSemantics.reduct M).mem y Y := by
  obtain ⟨v,hv,hvY⟩ := h
  exact ForcingWithTopCarrier.single_unique hM hv hy ▸ hvY

def Restricted (Y p q : M.Carrier .set) : Prop := ∀ z,
  (Project.FirstOrderSemantics.reduct M).mem z q ↔
    (Project.FirstOrderSemantics.reduct M).mem z p ∧ SomeIn Y z

def restricted {m} (Y p q : Fin m) : Project.Formula 1 m := .forallE (.iff
  (.mem .newest (.bound q.succ)) (.conj (.mem .newest (.bound p.succ)) (someIn Y.succ 0)))
derive_free_closed restricted

theorem restricted_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (Y p q : Fin m) :
    Project.Formula.satisfies ρ (restricted Y p q) ↔ Restricted (ρ.bound Y) (ρ.bound p) (ρ.bound q) := by
  simp only [restricted,Restricted,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,someIn_semantics hM]
  rfl

def Covered (p Y : M.Carrier .set) : Prop :=
  ∀ z, (Project.FirstOrderSemantics.reduct M).mem z p → SomeIn Y z

def covered {m} (p Y : Fin m) : Project.Formula 1 m := .forallE
  (.imp (.mem .newest (.bound p.succ)) (someIn Y.succ 0))
derive_free_closed covered

theorem covered_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (p Y : Fin m) :
    Project.Formula.satisfies ρ (covered p Y) ↔ Covered (ρ.bound p) (ρ.bound Y) := by
  simp only [covered,Covered,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,someIn_semantics hM]
  rfl

theorem restricted_subset {Y p q : M.Carrier .set} (h : Restricted Y p q) :
    (Project.FirstOrderSemantics.reduct M).MemberSubset q p := fun z hz => ((h z).mp hz).1

theorem restricted_covered {Y p q : M.Carrier .set} (h : Restricted Y p q) : Covered q Y :=
  fun z hz => ((h z).mp hz).2

theorem restricted_unique (hM : FirstOrder.Theory.Models M nativeZF) {Y p q r : M.Carrier .set}
    (hq : Restricted Y p q) (hr : Restricted Y p r) : q = r :=
  (ModelTransfer.extensionality hM).eq_of_same_members q r (fun z => (hq z).trans (hr z).symm)

theorem restricted_edge {Y p q a b : M.Carrier .set} (h : Restricted Y p q) :
    PureKuratowski.PairMember M a b q ↔
      ∃ z, PureKuratowski.Code M z a b ∧ (Project.FirstOrderSemantics.reduct M).mem z p ∧ SomeIn Y z := by
  exact ⟨fun ⟨z,hz,hm⟩ => ⟨z,hz,(h z).mp hm⟩,
    fun ⟨z,hz,hm⟩ => ⟨z,hz,(h z).mpr hm⟩⟩

theorem restricted_condition (hM : FirstOrder.Theory.Models M nativeZF) {S w Y p q : M.Carrier .set}
    (hp : Condition S w p) (h : Restricted Y p q) : Condition S w q := by
  have hsub := restricted_subset h
  refine ⟨fun z hz => hp.1 z (hsub z hz),?_,ForcingSupportSize.small_subset hM hsub hp.2.2⟩
  intro a b c hab hac
  exact hp.2.1 a b c (by obtain ⟨z,hz,hm⟩ := hab; exact ⟨z,hz,hsub z hm⟩)
    (by obtain ⟨z,hz,hm⟩ := hac; exact ⟨z,hz,hsub z hm⟩)

theorem restricted_compatible {S w Y p q : M.Carrier .set}
    (hp : Condition S w p) (h : Restricted Y p q) : Compatible q p := by
  intro a b c hab hac
  obtain ⟨z,hz,hm⟩ := hab
  exact hp.2.1 a b c ⟨z,hz,restricted_subset h z hm⟩ hac

theorem exists_restriction (hM : FirstOrder.Theory.Models M nativeZF) (Y p : M.Carrier .set) :
    ∃ q, Restricted Y p q := by
  let ρ : Env (Project.FirstOrderSemantics.reduct M) 1 := ⟨fun _ => Y,fun _ => Y⟩
  let φ : Project.UnarySchema 1 := {body := someIn (1 : Fin 2) 0, freeClosed := someIn_freeClosed _ _}
  obtain ⟨q,hq⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) φ ρ p
  refine ⟨q,fun z => (hq z).trans (and_congr Iff.rfl ?_)⟩
  exact someIn_semantics hM (ρ.push z) 1 0

/-- Exact source hcode, retaining ALL internal omega indices. -/
theorem code_into (hM : FirstOrder.Theory.Models M nativeZF) {w W p f Y e : M.Carrier .set}
    (hf : ForcingCohenCodes.Code w W p f) (hp : Covered p Y) (he : Empty e)
    (heY : (Project.FirstOrderSemantics.reduct M).mem e Y) : ForcingSupportSize.MapsTo w Y f := by
  refine ⟨hf.1.1,fun n y hny => ?_⟩
  rcases (hf.2 y).mp ⟨n,hny⟩ with hy | ⟨z,hz,hy⟩
  · exact ForcingWithTopCarrier.empty_unique hM he hy ▸ heY
  · exact someIn_member hM (hp z hz) hy

/-- Source hbgraph: code values in Y cover every actual graph entry. -/
theorem covered_of_code {w W p f Y : M.Carrier .set}
    (hf : ForcingCohenCodes.Code w W p f) (hY : ForcingSupportSize.MapsTo w Y f)
    (hM : FirstOrder.Theory.Models M nativeZF) : Covered p Y := by
  intro z hz
  obtain ⟨y,hy⟩ := ForcingWithTopCarrier.exists_single hM z
  obtain ⟨n,hn⟩ := (hf.2 y).mpr (Or.inr ⟨z,hz,hy⟩)
  exact ⟨y,hy,hY.2 n y hn⟩

def restrictionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4 (.imp
    (ProjectSyntax.encode id (ForcingCohenConditions.condition (0 : Fin 4) 1 2))
    (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (1 : Fin 5) 2 0))
      (.conj (restricted (4 : Fin 5) 3 0) (.conj (covered (0 : Fin 5) 4)
        (ConstructionCompatiblePlacement.compatible (0 : Fin 5) 3))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    restricted_freeClosed,covered_freeClosed,ConstructionCompatiblePlacement.compatible_freeClosed]

theorem restriction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence restrictionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) restrictionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),restricted_semantics hM,covered_semantics hM,
    ConstructionCompatiblePlacement.compatible_semantics hM]
  intro hp
  obtain ⟨q,hq⟩ := exists_restriction hM (bound 3) (bound 2)
  exact ⟨q,restricted_condition hM hp hq,hq,restricted_covered hq,restricted_compatible hp hq⟩

theorem restriction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence restrictionSentence) := ModelTransfer.derives (fun _ hM => restriction_models hM)

end PPAC.Migration.ForcingCohenRestriction
