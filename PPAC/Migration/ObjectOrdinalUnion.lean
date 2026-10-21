import PPAC.Migration.OrdinalStrictBound

/-! 任意内部原序数族的实际并、最小上界、唯一性和严格上界；完整原核闭句。 -/
namespace PPAC.Migration.ObjectOrdinalUnion
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalFamilySyntax InsertSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.foundation ∨
  q = Source.SetLanguage.separation OrdinalDifference.outsideMatrix ∨ q = Source.SetLanguage.union

def strictAssumptions : Theory := fun q => assumptions q ∨ q = Source.SetLanguage.pairing

def familySentence : Source.Sentence := ((transitiveSet (0 : Fin 1)).imp ((ordinals 0).imp (ordinal 0))).close

def unionSentence : Source.Sentence := ((ordinals (0 : Fin 2)).imp ((unionOf 1 0).imp (ordinal 1))).close

def leastSentence : Source.Sentence := ((unionOf (1 : Fin 2) 0).imp (leastUpper 1 0)).close

def uniqueSentence : Source.Sentence := ((leastUpper (0 : Fin 3) 2).imp ((leastUpper 1 2).imp (.equal 0 1))).close

def existenceSentence : Source.Sentence := ((ordinals (0 : Fin 1)).imp (ordinalUnionExists 0)).close

def strictSentence : Source.Sentence := ((ordinals (0 : Fin 1)).imp (OrdinalStrictBound.boundExists 0)).close

theorem ext_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
  .hyp ⟨_, Or.inl rfl, rfl⟩

theorem foundation_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.foundation.rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩

theorem separation_at (m : Nat) : Derives (assumptions.at m)
    ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩

theorem union_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.union.rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩

theorem source_family : Derives (assumptions.at 0) familySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact OrdinalFamilyOrder.ordinal_of_transitive 0 (add (add (ext_at 1) _) _)
    (add (add (foundation_at 1) _) _) (add (add (separation_at 1) _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_union : Derives (assumptions.at 0) unionSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact OrdinalUnion.ordinal 1 0 (add (add (ext_at 2) _) _)
    (add (add (foundation_at 2) _) _) (add (add (separation_at 2) _) _)
    (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem source_least : Derives (assumptions.at 0) leastSentence := by
  apply close_derives
  apply Derives.impI
  exact UnionUpperBounds.least 1 0 (.hyp (Or.inl rfl))

theorem source_unique : Derives (assumptions.at 0) uniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact UnionUpperBounds.unique 0 1 2 (add (add (ext_at 3) _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_existence : Derives (assumptions.at 0) existenceSentence := by
  apply close_derives
  apply Derives.impI
  exact OrdinalUnion.exists_union 0 (add (ext_at 1) _) (add (foundation_at 1) _)
    (add (separation_at 1) _) (add (union_at 1) _) (.hyp (Or.inl rfl))

theorem strict_at {m} {p : Formula m} (h : Derives (assumptions.at m) p) : Derives (strictAssumptions.at m) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨r, hr, heq⟩
  exact ⟨r, Or.inl hr, heq⟩

theorem source_strict : Derives (strictAssumptions.at 0) strictSentence := by
  apply close_derives
  apply Derives.impI
  have hp : Derives (strictAssumptions.at 1) (Source.SetLanguage.pairing.rename Fin.elim0) := .hyp ⟨_, Or.inr rfl, rfl⟩
  exact OrdinalStrictBound.exists_bound 0 (add (strict_at (ext_at 1)) _) (add (strict_at (foundation_at 1)) _)
    (add (strict_at (separation_at 1)) _) (add (strict_at (union_at 1)) _) (add hp _) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation OrdinalDifference.outsideMatrix, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact ZFEquivalence.source_foundation
  · exact SeparationSyntax.source_separation OrdinalDifference.outsideMatrix
  · exact ZFEquivalence.source_union

theorem family_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence familySentence) := TheoryTransport.sentence source_family

theorem source_ZF_family : Derives (Source.SetLanguage.ZF.at 0) familySentence := source_ZF_replay source_family

theorem native_family : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence familySentence) :=
  native_replay family_kernel_certificate

theorem union_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence unionSentence) := TheoryTransport.sentence source_union

theorem source_ZF_union : Derives (Source.SetLanguage.ZF.at 0) unionSentence := source_ZF_replay source_union

theorem native_union : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence unionSentence) :=
  native_replay union_kernel_certificate

theorem least_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence leastSentence) := TheoryTransport.sentence source_least

theorem source_ZF_least : Derives (Source.SetLanguage.ZF.at 0) leastSentence := source_ZF_replay source_least

theorem native_least : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence leastSentence) :=
  native_replay least_kernel_certificate

theorem unique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence uniqueSentence) := TheoryTransport.sentence source_unique

theorem source_ZF_unique : Derives (Source.SetLanguage.ZF.at 0) uniqueSentence := source_ZF_replay source_unique

theorem native_unique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence uniqueSentence) :=
  native_replay unique_kernel_certificate

theorem existence_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence existenceSentence) := TheoryTransport.sentence source_existence

theorem source_ZF_existence : Derives (Source.SetLanguage.ZF.at 0) existenceSentence := source_ZF_replay source_existence

theorem native_existence : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  native_replay existence_kernel_certificate

theorem strict_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory strictAssumptions) []
    (Translation.sentence strictSentence) := TheoryTransport.sentence source_strict

theorem source_ZF_strict : Derives (Source.SetLanguage.ZF.at 0) strictSentence := by
  refine Derives.weaken ?_ source_strict
  rintro q ⟨_, hr, rfl⟩
  rcases hr with hr | rfl
  · rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
    · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
    · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation OrdinalDifference.outsideMatrix, rfl⟩
    · exact ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩

theorem native_strict : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence strictSentence) := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := strict_kernel_certificate)
  rintro q ⟨_, hr, rfl⟩
  rcases hr with hr | rfl
  · rcases hr with rfl | rfl | rfl | rfl
    · exact ZFEquivalence.source_extensionality
    · exact ZFEquivalence.source_foundation
    · exact SeparationSyntax.source_separation OrdinalDifference.outsideMatrix
    · exact ZFEquivalence.source_union
  · exact ZFEquivalence.source_pairing
end PPAC.Migration.ObjectOrdinalUnion
