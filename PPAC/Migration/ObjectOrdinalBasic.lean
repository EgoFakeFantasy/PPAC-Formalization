import PPAC.Migration.OrdinalSuccessor

/-! 原Source序数的内部良基条件、空序数、成员和实际后继构造；原核闭句。 -/
namespace PPAC.Migration.ObjectOrdinalBasic
open Source SourceAlgebra SourceLogic OrdinalSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.foundation ∨ q = Source.SetLanguage.emptySet ∨
  q = Source.SetLanguage.pairing ∨ q = Source.SetLanguage.union

def wellFoundedSentence : Source.Sentence := (wellFounded (0 : Fin 1)).close

def noSelfSentence : Source.Sentence := ((ordinal (0 : Fin 1)).imp (Formula.mem 0 0).neg).close

def emptySentence : Source.Sentence := ((OmegaSyntax.empty (0 : Fin 1)).imp (ordinal 0)).close

def memberSentence : Source.Sentence := ((ordinal (0 : Fin 2)).imp ((Formula.mem 1 0).imp (ordinal 1))).close

def successorSentence : Source.Sentence := ((ordinal (0 : Fin 2)).imp ((OmegaSyntax.successor 1 0).imp (ordinal 1))).close

def emptyOrdinalExists (m : Nat) : Formula m := .ex ((OmegaSyntax.empty (Fin.last m)).conj (ordinal (Fin.last m)))

def existsEmptySentence : Source.Sentence := emptyOrdinalExists 0

def successorOrdinalExists {m} (a : Fin m) : Formula m := .ex
  ((OmegaSyntax.successor (Fin.last m) a.castSucc).conj (ordinal (Fin.last m)))

def existsSuccessorSentence : Source.Sentence := ((ordinal (0 : Fin 1)).imp (successorOrdinalExists 0)).close

theorem emptyOrdinalExists_rename {m k} (ρ : Fin m → Fin k) :
    (emptyOrdinalExists m).rename ρ = emptyOrdinalExists k := by
  simp only [emptyOrdinalExists, Formula.rename, OmegaSyntax.empty_rename, ordinal_rename, Formula.liftRen, Fin.lastCases_last]

theorem successorOrdinalExists_rename {m k} (a : Fin m) (ρ : Fin m → Fin k) :
    (successorOrdinalExists a).rename ρ = successorOrdinalExists (ρ a) := by
  simp only [successorOrdinalExists, Formula.rename, OmegaSyntax.successor_rename, ordinal_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem source_wellFounded : Derives (assumptions.at 0) wellFoundedSentence := by
  apply close_derives
  exact OrdinalFoundation.wellFounded 0 (.hyp ⟨_, Or.inl rfl, rfl⟩)

theorem source_noSelf : Derives (assumptions.at 0) noSelfSentence := by
  apply close_derives
  apply Derives.impI
  exact OrdinalEmpty.no_self 0 (.conjL (.conjR (Derives.hyp (Or.inl rfl))))

theorem source_empty : Derives (assumptions.at 0) emptySentence := by
  apply close_derives
  apply Derives.impI
  have hf : Derives (assumptions.at 1) (Source.SetLanguage.foundation.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  exact OrdinalEmpty.ordinal 0 (add hf _) (.hyp (Or.inl rfl))

theorem source_member : Derives (assumptions.at 0) memberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRestriction.member 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_successor : Derives (assumptions.at 0) successorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have hf : Derives (assumptions.at 2) (Source.SetLanguage.foundation.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  exact OrdinalSuccessor.ordinal 1 0 (add (add hf _) _) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem source_existsEmpty : Derives (assumptions.at 0) existsEmptySentence := by
  have he0 : Derives (assumptions.at 0) (Source.SetLanguage.emptySet.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  have hf : Derives (assumptions.at 0) (Source.SetLanguage.foundation.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have he := ObjectTransitiveCover.empty_exists_at he0
  let Z := OmegaSyntax.empty (Fin.last 0)
  let Γz := Context.add Z (Context.image Formula.raise (assumptions.at 0))
  apply Derives.exE (p := Z) he
  have hfZ : Derives Γz (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf Z
  have hZ : Derives Γz Z := .hyp (Or.inl rfl)
  have ho := OrdinalEmpty.ordinal (Fin.last 0) hfZ hZ
  have hr : Derives Γz (emptyOrdinalExists 1) := by
    apply Derives.exI (Fin.last 0)
    simpa only [Formula.instantiate, Formula.rename, OmegaSyntax.empty_rename, ordinal_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hZ ho
  simpa only [existsEmptySentence, Formula.raise, emptyOrdinalExists_rename] using hr

theorem source_existsSuccessor : Derives (assumptions.at 0) existsSuccessorSentence := by
  apply close_derives
  apply Derives.impI
  have hp : Derives (assumptions.at 1) (Source.SetLanguage.pairing.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  have hu : Derives (assumptions.at 1) (Source.SetLanguage.union.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
  have hf : Derives (assumptions.at 1) (Source.SetLanguage.foundation.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  let Δ := Context.add (ordinal (0 : Fin 1)) (assumptions.at 1)
  have ha : Derives Δ (ordinal 0) := .hyp (Or.inl rfl)
  have he := InsertExistence.exists_insert (Γ := Δ) (0 : Fin 1) 0 (add hp _) (add hu _)
  let S := OmegaSyntax.successor (Fin.last 1) (0 : Fin 1).castSucc
  let Γs := Context.add S (Context.image Formula.raise Δ)
  change Derives Δ (.ex S) at he
  apply Derives.exE (p := S) he
  have hfS : Derives Γs (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under (add hf _) S
  have haS : Derives Γs (ordinal (0 : Fin 1).castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha S
  have hS : Derives Γs S := .hyp (Or.inl rfl)
  have ho := OrdinalSuccessor.ordinal (Fin.last 1) (0 : Fin 1).castSucc hfS hS haS
  have hr : Derives Γs (successorOrdinalExists (0 : Fin 1).castSucc) := by
    apply Derives.exI (Fin.last 1)
    simpa only [Formula.instantiate, Formula.rename, OmegaSyntax.successor_rename, ordinal_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hS ho
  simpa only [Formula.raise, successorOrdinalExists_rename] using hr

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.emptySet, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl
  · exact ZFEquivalence.source_foundation
  · exact ZFEquivalence.source_emptySet
  · exact ZFEquivalence.source_pairing
  · exact ZFEquivalence.source_union

theorem wellFounded_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence wellFoundedSentence) := TheoryTransport.sentence source_wellFounded

theorem source_ZF_wellFounded : Derives (Source.SetLanguage.ZF.at 0) wellFoundedSentence := source_ZF_replay source_wellFounded

theorem native_wellFounded : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence wellFoundedSentence) :=
  native_replay wellFounded_kernel_certificate

theorem noSelf_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence noSelfSentence) := TheoryTransport.sentence source_noSelf

theorem source_ZF_noSelf : Derives (Source.SetLanguage.ZF.at 0) noSelfSentence := source_ZF_replay source_noSelf

theorem native_noSelf : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence noSelfSentence) :=
  native_replay noSelf_kernel_certificate

theorem empty_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence emptySentence) := TheoryTransport.sentence source_empty

theorem source_ZF_empty : Derives (Source.SetLanguage.ZF.at 0) emptySentence := source_ZF_replay source_empty

theorem native_empty : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence emptySentence) :=
  native_replay empty_kernel_certificate

theorem member_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence memberSentence) := TheoryTransport.sentence source_member

theorem source_ZF_member : Derives (Source.SetLanguage.ZF.at 0) memberSentence := source_ZF_replay source_member

theorem native_member : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence memberSentence) :=
  native_replay member_kernel_certificate

theorem successor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence successorSentence) := TheoryTransport.sentence source_successor

theorem source_ZF_successor : Derives (Source.SetLanguage.ZF.at 0) successorSentence := source_ZF_replay source_successor

theorem native_successor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence successorSentence) :=
  native_replay successor_kernel_certificate

theorem existsEmpty_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence existsEmptySentence) := TheoryTransport.sentence source_existsEmpty

theorem source_ZF_existsEmpty : Derives (Source.SetLanguage.ZF.at 0) existsEmptySentence := source_ZF_replay source_existsEmpty

theorem native_existsEmpty : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence existsEmptySentence) :=
  native_replay existsEmpty_kernel_certificate

theorem existsSuccessor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence existsSuccessorSentence) := TheoryTransport.sentence source_existsSuccessor

theorem source_ZF_existsSuccessor : Derives (Source.SetLanguage.ZF.at 0) existsSuccessorSentence := source_ZF_replay source_existsSuccessor

theorem native_existsSuccessor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence existsSuccessorSentence) :=
  native_replay existsSuccessor_kernel_certificate
end PPAC.Migration.ObjectOrdinalBasic
