/- Exact original bare constructible-history formulas in arbitrary native ZF models.
The data is the pinned existing syntax; semantic adapters connect its Kuratowski
entries and three-way local rule to the already proved internal recursion. -/
import PPAC.Migration.GodelDefRecursion

namespace PPAC.Migration.ConstructibleHistory
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ExistingConstructible
open Constructible (FOFormula Delta0Formula)
open Constructible.Model
open GodelDefOutput (toSource)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
attribute [local irreducible] Constructible.Godel.RudimentaryTerm.stackProgramEvalFormula
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
universe u
variable {A : Type u} {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem deMorgan (p q : Prop) : (¬ (¬ p ∧ ¬ q)) ↔ p ∨ q := by
  classical
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inl hp
    · exact Or.inr (Classical.byContradiction (fun hq => h ⟨hp, hq⟩))
  · rintro (hp | hq) ⟨hnp, hnq⟩
    · exact hnp hp
    · exact hnq hq

theorem disj_semantics (E : A → A → Prop) {n : Nat} (p q : FOFormula n) (v : Fin n → A) :
    Source.Formula.Realize E v (toSource (FOFormula.disj p q)) ↔
      Source.Formula.Realize E v (toSource p) ∨ Source.Formula.Realize E v (toSource q) := by
  classical
  simp only [FOFormula.disj, toSource, Source.Formula.Realize]
  exact deMorgan _ _

theorem boundedAll_semantics (E : A → A → Prop) {n : Nat} (i : Fin n)
    (p : Delta0Formula (n+1)) (v : Fin n → A) :
    Source.Formula.Realize E v (toSource (Delta0Formula.toFO (Delta0Formula.boundedAll i p))) ↔
      ∀ x, E x (v i) → Source.Formula.Realize E (Fin.lastCases x v) (toSource p.toFO) := by
  classical
  simp only [Delta0Formula.boundedAll, Delta0Formula.toFO, FOFormula.boundedEx,
    toSource, Source.Formula.Realize, Fin.lastCases_last, Fin.lastCases_castSucc,
    ]
  constructor
  · intro h x hx
    exact Classical.byContradiction (fun hn => h ⟨x, hx, hn⟩)
  · rintro h ⟨x, hx, hn⟩
    exact hn (h x hx)

theorem single_semantics {n : Nat} (v : Fin n → M.Carrier .set) (s x : Fin n) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v
      (toSource (Delta0Formula.singletonEqAt s x).toFO) ↔ PureKuratowski.Single M (v s) (v x) := by
  simp only [Delta0Formula.singletonEqAt, Delta0Formula.toFO, toSource, Source.Formula.Realize,
    boundedAll_semantics, Fin.lastCases_last, Fin.lastCases_castSucc]
  change ((_ ∧ ∀ z, _ → z = v x) ↔ ∀ z, _ ↔ z = v x)
  constructor
  · rintro ⟨hx, hu⟩ z
    exact ⟨hu z, fun h => h ▸ hx⟩
  · intro h
    exact ⟨(h (v x)).mpr rfl, fun z => (h z).mp⟩

theorem pair_semantics {n : Nat} (v : Fin n → M.Carrier .set) (s x y : Fin n) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v
      (toSource (Delta0Formula.unorderedPairEqAt s x y).toFO) ↔ PureKuratowski.Pair M (v s) (v x) (v y) := by
  simp only [Delta0Formula.unorderedPairEqAt, Delta0Formula.toFO, toSource, Source.Formula.Realize,
    boundedAll_semantics, Delta0Formula.disj, Fin.lastCases_last, Fin.lastCases_castSucc]
  classical
  change ((_ ∧ _ ∧ ∀ z, _ → ¬ (¬ z = v x ∧ ¬ z = v y)) ↔ ∀ z, _ ↔ z = v x ∨ z = v y)
  simp only [deMorgan]
  constructor
  · rintro ⟨hx, hy, hu⟩ z
    exact ⟨hu z, fun h => h.elim (fun h => h ▸ hx) (fun h => h ▸ hy)⟩
  · intro h
    exact ⟨(h (v x)).mpr (Or.inl rfl), (h (v y)).mpr (Or.inr rfl), fun z => (h z).mp⟩

theorem code_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (v : Fin n → M.Carrier .set) (p x y : Fin n) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v
      (toSource (Delta0Formula.kuratowskiPairEqAt p x y).toFO) ↔
        PureKuratowski.Code M (v p) (v x) (v y) := by
  simp only [Delta0Formula.kuratowskiPairEqAt, Delta0Formula.toFO, FOFormula.boundedEx,
    toSource, Source.Formula.Realize, single_semantics, pair_semantics, boundedAll_semantics,
    Delta0Formula.disj, Fin.lastCases_last, Fin.lastCases_castSucc]
  classical
  change ((∃ s, _ ∧ PureKuratowski.Single M s (v x)) ∧
    (∃ t, _ ∧ PureKuratowski.Pair M t (v x) (v y)) ∧
    (∀ z, _ → ¬ (¬ PureKuratowski.Single M z (v x) ∧ ¬ PureKuratowski.Pair M z (v x) (v y)))) ↔ _
  simp only [deMorgan]
  constructor
  · rintro ⟨⟨s, hs, hSingle⟩, ⟨t, ht, hPair⟩, hAll⟩
    refine ⟨s, t, hSingle, hPair, ?_⟩
    intro z
    constructor
    · intro hz
      rcases hAll z hz with h | h
      · exact Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members z s
          (fun a => (h a).trans (hSingle a).symm))
      · exact Or.inr ((ModelTransfer.extensionality hM).eq_of_same_members z t
          (fun a => (h a).trans (hPair a).symm))
    · rintro (rfl | rfl) <;> assumption
  · rintro ⟨s, t, hSingle, hPair, hOuter⟩
    refine ⟨⟨s, (hOuter s).mpr (Or.inl rfl), hSingle⟩,
      ⟨t, (hOuter t).mpr (Or.inr rfl), hPair⟩, ?_⟩
    intro z hz
    rcases (hOuter z).mp hz with rfl | rfl
    · exact Or.inl hSingle
    · exact Or.inr hPair

theorem entry_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (v : Fin n → M.Carrier .set) (h i s : Fin n) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v
      (toSource (bareHistoryEntryAt h i s)) ↔
      (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) (v i) (v s) (v h) := by
  simp only [bareHistoryEntryAt, toSource, Source.Formula.Realize, code_semantics hM,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  exact exists_congr (fun _ => and_comm)

theorem successor_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (v : Fin n → M.Carrier .set) (s p : Fin n) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v
      (toSource (Delta0Formula.successorFOAt s p)) ↔
      (Project.FirstOrderSemantics.reduct M).SuccessorOf (v s) (v p) := by
  simp only [Delta0Formula.successorFOAt, Delta0Formula.successorAt, Delta0Formula.toFO,
    toSource, Source.Formula.Realize, boundedAll_semantics, Delta0Formula.disj,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  classical
  change ((_ ∧ (∀ z, _ → ¬ (¬ _ ∧ ¬ z = v p)) ∧ (∀ z, _ → _)) ↔ ∀ z, _ ↔ _)
  simp only [deMorgan]
  constructor
  · rintro ⟨hp, hUpper, hLower⟩ z
    constructor
    · intro hz
      exact (hUpper z hz).elim Or.inl (fun h => Or.inr (h ▸ (fun _ => Iff.rfl)))
    · rintro (hz | hz)
      · exact hLower z hz
      · exact ((ModelTransfer.extensionality hM).eq_of_same_members z (v p) hz) ▸ hp
  · intro h
    refine ⟨(h (v p)).mpr (Or.inr fun _ => Iff.rfl), ?_, ?_⟩
    · intro z hz
      exact ((h z).mp hz).elim Or.inl
        (fun hs => Or.inr ((ModelTransfer.extensionality hM).eq_of_same_members z (v p) hs))
    · intro z hz
      exact (h z).mpr (Or.inl hz)

attribute [local irreducible] Constructible.Godel.RudimentaryTerm.godelDefOutputFormula

def state (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (history index stage : M.Carrier .set) : Fin 16 → M.Carrier .set :=
  Fin.lastCases stage (Fin.lastCases index (Fin.lastCases history (fun i => env.bound i.rev)))

def localState (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (history index stage : M.Carrier .set) : Prop :=
  (index = env.bound 10 ∧ stage = env.bound 10) ∨
  (∃ predecessor previous,
    (Project.FirstOrderSemantics.reduct M).SuccessorOf index predecessor ∧
    (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) predecessor previous history ∧
    GodelDefRecursion.successor.denote env previous stage) ∨
  (index ≠ env.bound 10 ∧ ¬ ∃ predecessor,
    (Project.FirstOrderSemantics.reduct M).SuccessorOf index predecessor) ∧
  (∀ z, (Project.FirstOrderSemantics.reduct M).mem z stage ↔
    ∃ earlier, (Project.FirstOrderSemantics.reduct M).mem earlier index ∧
      ∃ previous, (Project.FirstOrderSemantics.reduct M).PairMember
        (KuratowskiZF.interpretation hM) earlier previous history ∧
        (Project.FirstOrderSemantics.reduct M).mem z previous)

theorem successor_state_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (history index stage : M.Carrier .set) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (state env history index stage)
      (toSource bareHistorySuccessorStateFormula) ↔
    ∃ predecessor previous,
      (Project.FirstOrderSemantics.reduct M).SuccessorOf index predecessor ∧
      (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) predecessor previous history ∧
      GodelDefRecursion.successor.denote env previous stage := by
  simp only [bareHistorySuccessorStateFormula, toSource, Source.Formula.Realize,
    successor_semantics hM, entry_semantics hM, GodelDefOutput.toSource_rename,
    DefinableMinimaChoice.realize_rename]
  apply exists_congr
  intro predecessor
  apply exists_congr
  intro previous
  change (_ ∧ _ ∧ Source.Formula.Realize _ _ GodelDefOutput.output) ↔ _
  rw [GodelDefRecursion.successor_semantics hM env previous stage]
  have he : (fun i => Fin.lastCases previous
      (Fin.lastCases predecessor (state env history index stage)) (bareHistorySuccessorDefRename i)) =
      Fin.lastCases stage (Fin.cases previous (fun i : Fin 13 => env.bound i.rev)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · simp only [bareHistorySuccessorDefRename, Fin.lastCases_castSucc, Fin.cases_succ]
        change Fin.lastCases previous (Fin.lastCases predecessor (state env history index stage))
          (Fin.castLE (by decide) k) = env.bound k.rev
        have hk : (Fin.castLE (by decide) k : Fin 18) = k.castSucc.castSucc.castSucc.castSucc.castSucc := by
          apply Fin.ext
          rfl
        rw [hk]
        simp only [state, Fin.lastCases_castSucc]
  rw [he]
  rfl

theorem limit_state_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (v : Fin 3 → M.Carrier .set) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v
      (toSource bareHistoryLimitStateFormula) ↔
    ∀ z, (Project.FirstOrderSemantics.reduct M).mem z (v 2) ↔
      ∃ earlier, (Project.FirstOrderSemantics.reduct M).mem earlier (v 1) ∧
        ∃ previous, (Project.FirstOrderSemantics.reduct M).PairMember
          (KuratowskiZF.interpretation hM) earlier previous (v 0) ∧
          (Project.FirstOrderSemantics.reduct M).mem z previous := by
  rw [bareHistoryLimitStateFormula, GodelDefOutput.all_semantics]
  apply forall_congr'
  intro z
  rw [GodelDefOutput.iff_semantics]
  simp only [FOFormula.boundedEx, toSource, Source.Formula.Realize, entry_semantics hM]
  rfl

theorem local_state_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (history index stage : M.Carrier .set) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (state env history index stage)
      (toSource bareHistoryLocalStateFormula) ↔ localState hM env history index stage := by
  simp only [bareHistoryLocalStateFormula, disj_semantics, successor_state_semantics hM,
    bareHistoryBaseStateFormula, bareHistoryIndexIsZeroFormula, bareHistoryIndexHasPredecessorFormula,
    toSource, Source.Formula.Realize, successor_semantics hM,
    GodelDefOutput.toSource_rename, DefinableMinimaChoice.realize_rename, limit_state_semantics hM]
  rfl

def valid (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (history bound : M.Carrier .set) : Prop :=
  ∀ index, ((Project.FirstOrderSemantics.reduct M).mem index bound ∨ index = bound) →
    ∃ stage, (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) index stage history ∧
      (∀ other, (Project.FirstOrderSemantics.reduct M).PairMember
        (KuratowskiZF.interpretation hM) index other history → other = stage) ∧
      localState hM env history index stage

theorem valid_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (history bound : M.Carrier .set) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases bound (Fin.lastCases history (fun i : Fin 13 => env.bound i.rev)))
      (toSource bareValidStageHistoryFormula) ↔ valid hM env history bound := by
  rw [bareValidStageHistoryFormula, GodelDefOutput.all_semantics]
  apply forall_congr'
  intro index
  rw [GodelDefOutput.imp_semantics, disj_semantics]
  simp only [bareValidStageHistoryIndexBody, toSource, Source.Formula.Realize,
    entry_semantics hM, GodelDefOutput.all_semantics, GodelDefOutput.imp_semantics,
    GodelDefOutput.toSource_rename, DefinableMinimaChoice.realize_rename]
  change (_ → ∃ stage, _ ∧ (∀ other, _ → other = stage) ∧
    Source.Formula.Realize _ _ (toSource bareHistoryLocalStateFormula)) ↔ _
  apply imp_congr_right
  intro _
  apply exists_congr
  intro stage
  have he : (fun i => Fin.lastCases stage (Fin.lastCases index
      (Fin.lastCases bound (Fin.lastCases history (fun i : Fin 13 => env.bound i.rev))))
        (bareValidHistoryLocalRename i)) = state env history index stage := by
    funext i
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => Fin.lastCases ?_ (fun l => ?_) k) j) i
    · rfl
    · rfl
    · rfl
    · have hl : (Fin.castLE (by decide) l : Fin 17) = l.castSucc.castSucc.castSucc.castSucc := by
        apply Fin.ext
        rfl
      simp only [bareValidHistoryLocalRename, Fin.lastCases_castSucc]
      rw [hl]
      simp only [state, Fin.lastCases_castSucc]
  rw [he, local_state_semantics hM env history index stage]
  rfl

def stageFormula : Source.Formula 15 := toSource bareStageAtFormula

def stageSchema : Project.BinarySchema 13 := ProjectSyntax.binary stageFormula

theorem stage_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13) (index stage : M.Carrier .set) :
    stageSchema.denote env index stage ↔ ∃ history, valid hM env history index ∧
      (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) index stage history := by
  unfold stageSchema ProjectSyntax.binary ProjectSyntax.formula Project.BinarySchema.denote
  rw [GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM)]
  have hAssignment : (fun i : Fin 15 => ((env.push index).push stage).bound i.rev) =
      Fin.lastCases stage (Fin.lastCases index (fun i : Fin 13 => env.bound i.rev)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => ?_) j) i
    · rfl
    · rfl
    · simp only [Fin.rev_castSucc, SetTheory.Env.push, Fin.cases_succ, Fin.lastCases_castSucc]
  rw [hAssignment]
  simp only [stageFormula, bareStageAtFormula, toSource, Source.Formula.Realize,
    GodelDefOutput.toSource_rename, DefinableMinimaChoice.realize_rename, entry_semantics hM]
  apply exists_congr
  intro history
  have he : (fun i => Fin.lastCases history (Fin.lastCases stage (Fin.lastCases index
      (fun i : Fin 13 => env.bound i.rev))) (bareStageAtValidHistoryRename i)) =
      Fin.lastCases index (Fin.lastCases history (fun i : Fin 13 => env.bound i.rev)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => ?_) j) i
    · rfl
    · rfl
    · have hr : ∀ k : Fin 13, bareStageAtValidHistoryRename k.castSucc.castSucc =
          k.castSucc.castSucc.castSucc := by decide +kernel
      rw [hr k]
      simp only [Fin.lastCases_castSucc]
  rw [he, valid_semantics hM env history index]
  rfl

/-- Transport an actual step on the internal restriction to the original local history rule. -/
theorem local_of_step (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (hEmpty : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z (env.bound 10))
    {history index stage restricted : M.Carrier .set}
    (hSequence : (Project.FirstOrderSemantics.reduct M).IsSequenceOfLength
      (KuratowskiZF.interpretation hM) restricted index)
    (hRestriction : (Project.FirstOrderSemantics.reduct M).IsRestrictionOf
      (KuratowskiZF.interpretation hM) restricted history index)
    (hStep : GodelDefRecursion.operator.denote env restricted stage) :
    localState hM env history index stage := by
  have hExt := ModelTransfer.extensionality hM
  rcases (GodelDefRecursion.operator_semantics hM env restricted stage).mp hStep with hZero | hSucc | hLimit
  · obtain ⟨⟨zero, hZeroSequence, hZero⟩, hStage⟩ := hZero
    have hi := SetTheory.Structure.IsSequenceOfLength.length_eq hExt hSequence hZeroSequence
    have hz := hExt.eq_of_same_members zero (env.bound 10)
      (fun z => ⟨fun h => False.elim (hZero z h), fun h => False.elim (hEmpty z h)⟩)
    have hv := hExt.eq_of_same_members stage (env.bound 10)
      (fun z => ⟨fun h => False.elim (hStage z h), fun h => False.elim (hEmpty z h)⟩)
    exact Or.inl ⟨hi.trans hz, hv⟩
  · obtain ⟨previous, ⟨predecessor, hPredOrdinal, length, hSuccessor, hLength, hPrevious⟩, hOutput⟩ := hSucc
    have hi := SetTheory.Structure.IsSequenceOfLength.length_eq hExt hSequence hLength
    subst length
    exact Or.inr (Or.inl ⟨predecessor, previous, hSuccessor,
      ((hRestriction.2 predecessor previous).mp hPrevious).2, hOutput⟩)
  · obtain ⟨length, hLimitOrdinal, hLength, range, hRange, hUnion⟩ := hLimit
    have hi := SetTheory.Structure.IsSequenceOfLength.length_eq hExt hSequence hLength
    subst length
    have hNonzero : index ≠ env.bound 10 := by
      intro heq
      obtain ⟨z, hz⟩ := hLimitOrdinal.2.1
      exact hEmpty z (heq ▸ hz)
    have hNoPredecessor : ¬ ∃ predecessor,
        (Project.FirstOrderSemantics.reduct M).SuccessorOf index predecessor := by
      rintro ⟨predecessor, hSucc⟩
      have hp := hSucc.predecessor_mem
      obtain ⟨previous, hPrevious⟩ := (hSequence.2.2 predecessor).mp hp
      have hSuccessor : (Project.FirstOrderSemantics.reduct M).IsSuccessorLengthSequenceWithLast
          (KuratowskiZF.interpretation hM) restricted previous :=
        ⟨predecessor, hSequence.1.mem hp, index, hSucc, hSequence, hPrevious⟩
      exact hSuccessor.not_limitLength hExt ⟨index, hLimitOrdinal, hSequence, range, hRange, hUnion⟩
    refine Or.inr (Or.inr ⟨⟨hNonzero, hNoPredecessor⟩, ?_⟩)
    intro z
    rw [hUnion z]
    constructor
    · rintro ⟨previous, hPreviousRange, hz⟩
      obtain ⟨earlier, hEarlier⟩ := (hRange previous).mp hPreviousRange
      obtain ⟨hIndex, hFull⟩ := (hRestriction.2 earlier previous).mp hEarlier
      exact ⟨earlier, hIndex, previous, hFull, hz⟩
    · rintro ⟨earlier, hIndex, previous, hFull, hz⟩
      exact ⟨previous, (hRange previous).mpr
        ⟨earlier, (hRestriction.2 earlier previous).mpr ⟨hIndex, hFull⟩⟩, hz⟩

/-- The original local rule is also sufficient on a complete internal prefix sequence. -/
theorem step_of_local (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (hEmpty : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z (env.bound 10))
    {history index stage : M.Carrier .set}
    (hSequence : (Project.FirstOrderSemantics.reduct M).IsSequenceOfLength
      (KuratowskiZF.interpretation hM) history index)
    (hLocal : localState hM env history index stage) :
    GodelDefRecursion.operator.denote env history stage := by
  apply (GodelDefRecursion.operator_semantics hM env history stage).mpr
  have hExt := ModelTransfer.extensionality hM
  rcases hLocal with ⟨hIndex, hStage⟩ | ⟨predecessor, previous, hSucc, hPrevious, hOutput⟩ | ⟨⟨hNonzero, hNoPred⟩, hUnion⟩
  · subst index
    subst stage
    exact Or.inl ⟨⟨env.bound 10, hSequence, hEmpty⟩, hEmpty⟩
  · exact Or.inr (Or.inl ⟨previous,
      ⟨predecessor, hSequence.1.mem hSucc.predecessor_mem, index, hSucc, hSequence, hPrevious⟩, hOutput⟩)
  · have hLimit : (Project.FirstOrderSemantics.reduct M).IsLimitOrdinal index := by
      rcases hSequence.1.classify hExt with hZero | ⟨predecessor, _, hSucc⟩ | hLimit
      · exact False.elim (hNonzero (hExt.eq_of_same_members index (env.bound 10)
          (fun z => ⟨fun hz => False.elim (hZero z hz), fun hz => False.elim (hEmpty z hz)⟩)))
      · exact False.elim (hNoPred ⟨predecessor, hSucc⟩)
      · exact hLimit
    obtain ⟨range, hRange⟩ := SetTheory.ZF.exists_range_of_setFunction
      (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hSequence.2.1 hSequence.2.2
    refine Or.inr (Or.inr ⟨index, hLimit, hSequence, range, hRange, ?_⟩)
    intro z
    rw [hUnion z]
    constructor
    · rintro ⟨earlier, _, previous, hPrevious, hz⟩
      exact ⟨previous, (hRange previous).mpr ⟨earlier, hPrevious⟩, hz⟩
    · rintro ⟨previous, hPrevious, hz⟩
      obtain ⟨earlier, hEarlier⟩ := (hRange previous).mp hPrevious
      exact ⟨earlier, (hSequence.2.2 earlier).mpr ⟨previous, hEarlier⟩, previous, hEarlier, hz⟩

/-- Extra garbage in the original history is irrelevant: only entries below the index are used. -/
theorem local_transfer (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    {first second index stage : M.Carrier .set}
    (hEntries : ∀ earlier, (Project.FirstOrderSemantics.reduct M).mem earlier index → ∀ previous,
      (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) earlier previous first ↔
      (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) earlier previous second)
    (hLocal : localState hM env first index stage) : localState hM env second index stage := by
  rcases hLocal with hBase | ⟨predecessor, previous, hSucc, hPrevious, hOutput⟩ | ⟨hLimit, hUnion⟩
  · exact Or.inl hBase
  · exact Or.inr (Or.inl ⟨predecessor, previous, hSucc,
      (hEntries predecessor hSucc.predecessor_mem previous).mp hPrevious, hOutput⟩)
  · refine Or.inr (Or.inr ⟨hLimit, ?_⟩)
    intro z
    rw [hUnion z]
    constructor
    · rintro ⟨earlier, hi, previous, hp, hz⟩
      exact ⟨earlier, hi, previous, (hEntries earlier hi previous).mp hp, hz⟩
    · rintro ⟨earlier, hi, previous, hp, hz⟩
      exact ⟨earlier, hi, previous, (hEntries earlier hi previous).mpr hp, hz⟩

/-- The induction property is represented by this fixed pure first-order schema.
Parameters are `(fixed13,history,bound)`, internally, not a host truth predicate. -/
def comparisonSchema : Project.UnarySchema 15 where
  body := .imp (.disj (.mem Project.Term.newest (.bound 1))
      (Project.Formula.extensionalEq Project.Term.newest (.bound 1)))
    (.forallE (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention
      (.bound 1) Project.Term.newest (.bound 3))
      (Project.Formula.related GodelDefRecursion.hierarchy
        (Definitional.TermVector.boundParameters 13 4) (.bound 1) Project.Term.newest)))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

theorem comparison_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13) (history bound index : M.Carrier .set) :
    comparisonSchema.denote ((env.push history).push bound) index ↔
      ((Project.FirstOrderSemantics.reduct M).mem index bound ∨ index = bound) →
        ∀ stage, (Project.FirstOrderSemantics.reduct M).PairMember
          (KuratowskiZF.interpretation hM) index stage history →
          GodelDefRecursion.hierarchy.denote env index stage := by
  simp only [comparisonSchema, Project.UnarySchema.denote,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    Project.Formula.satisfies_related_iff, Definitional.TermVector.evalEnv_boundParameters_four,
    Project.Term.eval_bound_zero_push, Project.Term.eval_bound_one_push,
    Project.Term.eval_bound_two_push, Project.Term.eval_bound_three_push, Definitional.Term.eval_newest]

/-- Internal ordinal induction compares arbitrary original histories to the existing recursion.
The counterexample set comes from full ZF Separation on comparisonSchema.neg. -/
theorem valid_values (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (hEmpty : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z (env.bound 10))
    {history bound : M.Carrier .set}
    (hBound : (Project.FirstOrderSemantics.reduct M).IsOrdinal bound)
    (hValid : valid hM env history bound) :
    ∀ stage, (Project.FirstOrderSemantics.reduct M).PairMember
      (KuratowskiZF.interpretation hM) bound stage history →
      GodelDefRecursion.hierarchy.denote env bound stage := by
  let property : M.Carrier .set → Prop := fun index =>
    ((Project.FirstOrderSemantics.reduct M).mem index bound ∨ index = bound) →
      ∀ stage, (Project.FirstOrderSemantics.reduct M).PairMember
        (KuratowskiZF.interpretation hM) index stage history →
        GodelDefRecursion.hierarchy.denote env index stage
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨counterexamples, hCounterexamples⟩ := SetTheory.ZF.separation_exists_d hZF
    comparisonSchema.neg ((env.push history).push bound) bound
  have hCounter : ∀ index, (Project.FirstOrderSemantics.reduct M).mem index counterexamples ↔
      (Project.FirstOrderSemantics.reduct M).mem index bound ∧ ¬ property index := by
    intro index
    rw [hCounterexamples index]
    simp only [Project.UnarySchema.neg, Project.Formula.satisfies_neg_iff]
    change (_ ∧ ¬ comparisonSchema.denote ((env.push history).push bound) index) ↔ _
    rw [comparison_semantics hM env history bound index]
  have hAll : property bound := by
    apply SetTheory.Structure.IsOrdinal.induction hBound property ⟨counterexamples, hCounter⟩
    intro current hCurrent hPrevious hBelow stage hStage
    have below_previous : ∀ earlier, (Project.FirstOrderSemantics.reduct M).mem earlier current →
        (Project.FirstOrderSemantics.reduct M).mem earlier bound ∨ earlier = bound := by
      intro earlier hi
      rcases hBelow with hb | rfl
      · exact Or.inl (hBound.transitive current hb earlier hi)
      · exact Or.inl hi
    obtain ⟨_, hValue, _⟩ := GodelDefRecursion.hierarchy_total_unique hM env current hCurrent
    obtain ⟨sequence, hSequence, _⟩ := (Project.Formula.denote_transfiniteRecursion_iff
      (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM)
      env GodelDefRecursion.operator current _).mp hValue
    have hEntries : ∀ earlier, (Project.FirstOrderSemantics.reduct M).mem earlier current → ∀ previous,
        (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) earlier previous history ↔
        (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) earlier previous sequence := by
      intro earlier hi previous
      obtain ⟨selected, hSelected⟩ := (hSequence.1.2.2 earlier).mp hi
      have hSelectedValue : GodelDefRecursion.hierarchy.denote env earlier selected :=
        (Project.Formula.denote_transfiniteRecursion_iff (KuratowskiZF.interpretation hM)
          (ModelTransfer.extensionality hM) env GodelDefRecursion.operator earlier selected).mpr
          (hSequence.recursionValue_of_pairMember hi hSelected)
      have hInduction := hPrevious earlier hi (below_previous earlier hi)
      obtain ⟨value, hActual, hUnique⟩ := GodelDefRecursion.hierarchy_total_unique hM env earlier (hCurrent.mem hi)
      constructor
      · intro hp
        have heq := (hUnique previous (hInduction previous hp)).trans (hUnique selected hSelectedValue).symm
        exact heq.symm ▸ hSelected
      · intro hp
        obtain ⟨raw, hRaw, _, _⟩ := hValid earlier (below_previous earlier hi)
        have hPreviousValue := (Project.Formula.denote_transfiniteRecursion_iff
          (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM)
          env GodelDefRecursion.operator earlier previous).mpr (hSequence.recursionValue_of_pairMember hi hp)
        have heq := (hUnique previous hPreviousValue).trans (hUnique raw (hInduction raw hRaw)).symm
        exact heq.symm ▸ hRaw
    obtain ⟨raw, _, hRawUnique, hLocal⟩ := hValid current hBelow
    have hEq := hRawUnique stage hStage
    subst raw
    have hStep := step_of_local hM env hEmpty hSequence.1 (local_transfer hM env hEntries hLocal)
    exact (Project.Formula.denote_transfiniteRecursion_iff (KuratowskiZF.interpretation hM)
      (ModelTransfer.extensionality hM) env GodelDefRecursion.operator current stage).mpr ⟨sequence, hSequence, hStep⟩
  exact hAll (Or.inr rfl)

/-- Every internal ordinal has a history satisfying the literal original bareStageAt formula. -/
theorem stage_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (hEmpty : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z (env.bound 10))
    {index : M.Carrier .set} (hIndex : (Project.FirstOrderSemantics.reduct M).IsOrdinal index) :
    ∃ stage, stageSchema.denote env index stage := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hKP := SetTheory.ZF.modelsKP hZF
  obtain ⟨successor, hSuccessor⟩ := SetTheory.KP.exists_successor hKP index
  have hSuccessorOrdinal := SetTheory.KP.successor_isOrdinal hKP hIndex hSuccessor
  obtain ⟨history, hHistory⟩ := SetTheory.ZF.recursiveSequence_exists hZF
    (KuratowskiZF.interpretation hM) env GodelDefRecursion.operator
    (GodelDefRecursion.operator_total_unique hM env) hSuccessorOrdinal
  have hValid : valid hM env history index := by
    intro current hCurrent
    have hMember : (Project.FirstOrderSemantics.reduct M).mem current successor := by
      apply (hSuccessor current).mpr
      rcases hCurrent with hCurrent | rfl
      · exact Or.inl hCurrent
      · exact Or.inr (fun _ => Iff.rfl)
    obtain ⟨stage, hStage⟩ := (hHistory.1.2.2 current).mp hMember
    refine ⟨stage, hStage, (fun other hOther => hHistory.1.2.1.2 current other stage hOther hStage), ?_⟩
    obtain ⟨restricted, hRestriction, hStep⟩ := hHistory.2 current hMember stage hStage
    exact local_of_step hM env hEmpty (hHistory.restriction hMember hRestriction).1 hRestriction hStep
  obtain ⟨stage, hStage⟩ := (hHistory.1.2.2 index).mp hSuccessor.predecessor_mem
  exact ⟨stage, (stage_semantics hM env index stage).mpr ⟨history, hValid, hStage⟩⟩

/-- Exact equivalence, including arbitrary original histories with irrelevant members. -/
theorem stage_iff_hierarchy (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (hEmpty : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z (env.bound 10))
    {index : M.Carrier .set} (hIndex : (Project.FirstOrderSemantics.reduct M).IsOrdinal index)
    (stage : M.Carrier .set) :
    stageSchema.denote env index stage ↔ GodelDefRecursion.hierarchy.denote env index stage := by
  constructor
  · intro h
    obtain ⟨history, hValid, hStage⟩ := (stage_semantics hM env index stage).mp h
    exact valid_values hM env hEmpty hIndex hValid stage hStage
  · intro hStage
    obtain ⟨selected, hSelected⟩ := stage_exists hM env hEmpty hIndex
    obtain ⟨history, hValid, hEntry⟩ := (stage_semantics hM env index selected).mp hSelected
    have hSelectedValue := valid_values hM env hEmpty hIndex hValid selected hEntry
    obtain ⟨value, _, hUnique⟩ := GodelDefRecursion.hierarchy_total_unique hM env index hIndex
    have heq := (hUnique selected hSelectedValue).trans (hUnique stage hStage).symm
    exact heq ▸ hSelected

theorem stage_total_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (hEmpty : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z (env.bound 10)) :
    (Project.FirstOrderSemantics.reduct M).IsClassFunctionOnOrdinals (stageSchema.denote env) := by
  intro index hIndex
  obtain ⟨stage, hStage, hUnique⟩ := GodelDefRecursion.hierarchy_total_unique hM env index hIndex
  exact ⟨stage, (stage_iff_hierarchy hM env hEmpty hIndex stage).mpr hStage,
    fun other hOther => hUnique other ((stage_iff_hierarchy hM env hEmpty hIndex other).mp hOther)⟩

/-- Closed pure-language agreement with the existing internal Def recursion. -/
def agreementSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13 (.imp (Project.Formula.isEmpty (.bound 10))
    (.forallE (.imp (Project.Formula.isOrdinal Project.Term.newest) (.forallE
      (.iff (Project.Formula.related stageSchema (Definitional.TermVector.boundParameters 13 2)
          (.bound 1) Project.Term.newest)
        (Project.Formula.related GodelDefRecursion.hierarchy (Definitional.TermVector.boundParameters 13 2)
          (.bound 1) Project.Term.newest))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

def uniqueSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13 (.imp (Project.Formula.isEmpty (.bound 10))
    (Project.Formula.isClassFunctionOnOrdinals stageSchema (Definitional.TermVector.boundParameters 13 0)))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

theorem agreement_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence agreementSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) agreementSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_isOrdinal_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_related_iff,
    Definitional.TermVector.evalEnv_boundParameters_two,
    Project.Term.eval_bound_zero_push, Project.Term.eval_bound_one_push, Definitional.Term.eval_newest]
  intro hEmpty index hIndex stage
  exact stage_iff_hierarchy hM ⟨bound, free⟩ hEmpty hIndex stage

theorem unique_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence uniqueSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) uniqueSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isClassFunctionOnOrdinals_iff (ModelTransfer.extensionality hM),
    Definitional.TermVector.evalEnv_boundParameters_zero]
  intro hEmpty
  exact stage_total_unique hM ⟨bound, free⟩ hEmpty

theorem agreement_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence agreementSentence) :=
  ModelTransfer.derives (fun _ hM => agreement_models hM)

theorem unique_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence uniqueSentence) :=
  ModelTransfer.derives (fun _ hM => unique_models hM)

end PPAC.Migration.ConstructibleHistory
