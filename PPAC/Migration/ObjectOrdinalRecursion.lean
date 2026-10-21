import PPAC.Migration.OrdinalRecursionCompatibility

/-! 任意公式递归模式：限制保持/实际受限图、给定图相容和同域唯一的完整原核闭句。 -/
namespace PPAC.Migration.ObjectOrdinalRecursion
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionDeterminism

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.foundation ∨
  q = Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg ∨ q = Source.SetLanguage.separation RestrictionSyntax.matrix

def params3 {n} : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc

def params4 {n} : Fin n → Fin (n+4) := fun i => i.castSucc.castSucc.castSucc.castSucc

def preservationSentence {n} (p : Formula (n+3)) : Source.Sentence :=
  ((transitiveSet (Fin.last (n+2)).castSucc).imp ((subset (Fin.last (n+2)).castSucc (Fin.last (n+1)).castSucc.castSucc).imp
    ((restrict (Fin.last (n+3)) (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n+2)).castSucc).imp ((recursor p params4 (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc).imp (recursor p params4 (Fin.last (n+3)) (Fin.last (n+2)).castSucc))))).close

def restrictionSentence {n} (p : Formula (n+3)) : Source.Sentence :=
  ((transitiveSet (Fin.last (n+2))).imp ((subset (Fin.last (n+2)) (Fin.last (n+1)).castSucc).imp
    ((recursor p params3 (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).imp (OrdinalRecursionRestriction.restrictedExists p params3 (Fin.last n).castSucc.castSucc (Fin.last (n+2)))))).close

def compatibilitySentence {n} (p : Formula (n+3)) : Source.Sentence :=
  ((deterministic p params4).imp ((ordinal (Fin.last (n+2)).castSucc).imp ((ordinal (Fin.last (n+3))).imp
    ((recursor p params4 (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n+2)).castSucc).imp ((recursor p params4 (Fin.last (n+1)).castSucc.castSucc (Fin.last (n+3))).imp (GraphFamilySyntax.agrees (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc)))))).close

def uniquenessSentence {n} (p : Formula (n+3)) : Source.Sentence :=
  ((deterministic p params3).imp ((ordinal (Fin.last (n+2))).imp
    ((recursor p params3 (Fin.last n).castSucc.castSucc (Fin.last (n+2))).imp ((recursor p params3 (Fin.last (n+1)).castSucc (Fin.last (n+2))).imp (.equal (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc))))).close

theorem ext_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
  .hyp ⟨_, Or.inl rfl, rfl⟩

theorem foundation_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.foundation.rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩

theorem separation_at (m : Nat) : Derives (assumptions.at m)
    ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩

theorem restriction_at (m : Nat) : Derives (assumptions.at m)
    ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩

theorem source_preservation {n} (p : Formula (n+3)) : Derives (assumptions.at 0) (preservationSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionRestriction.recursor_restrict p params4 (Fin.last (n+3)) (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n+2)).castSucc (Fin.last (n+1)).castSucc.castSucc
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_restriction {n} (p : Formula (n+3)) : Derives (assumptions.at 0) (restrictionSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionRestriction.exists_restricted p params3 (Fin.last n).castSucc.castSucc (Fin.last (n+2)) (Fin.last (n+1)).castSucc
    (add (add (add (restriction_at (n+3)) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_compatibility {n} (p : Formula (n+3)) : Derives (assumptions.at 0) (compatibilitySentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionCompatibility.compatible p params4 (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc (Fin.last (n+2)).castSucc (Fin.last (n+3))
    (add (add (add (add (add (ext_at (n+4)) _) _) _) _) _)
    (add (add (add (add (add (foundation_at (n+4)) _) _) _) _) _)
    (add (add (add (add (add (separation_at (n+4)) _) _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_uniqueness {n} (p : Formula (n+3)) : Derives (assumptions.at 0) (uniquenessSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionCompatibility.unique_same_domain p params3 (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))
    (add (add (add (add (ext_at (n+3)) _) _) _) _)
    (add (add (add (add (foundation_at (n+3)) _) _) _) _)
    (add (add (add (add (separation_at (n+3)) _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation IterationSyntax.agreementMatrix.neg, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation RestrictionSyntax.matrix, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact ZFEquivalence.source_foundation
  · exact SeparationSyntax.source_separation IterationSyntax.agreementMatrix.neg
  · exact SeparationSyntax.source_separation RestrictionSyntax.matrix

theorem preservation_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence (preservationSentence p)) := TheoryTransport.sentence (source_preservation p)

theorem source_ZF_preservation {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (preservationSentence p) := source_ZF_replay (source_preservation p)

theorem native_preservation {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (preservationSentence p)) :=
  native_replay (preservation_kernel_certificate p)

theorem restriction_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence (restrictionSentence p)) := TheoryTransport.sentence (source_restriction p)

theorem source_ZF_restriction {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (restrictionSentence p) := source_ZF_replay (source_restriction p)

theorem native_restriction {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (restrictionSentence p)) :=
  native_replay (restriction_kernel_certificate p)

theorem compatibility_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence (compatibilitySentence p)) := TheoryTransport.sentence (source_compatibility p)

theorem source_ZF_compatibility {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (compatibilitySentence p) := source_ZF_replay (source_compatibility p)

theorem native_compatibility {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (compatibilitySentence p)) :=
  native_replay (compatibility_kernel_certificate p)

theorem uniqueness_kernel_certificate {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
      (Translation.sentence (uniquenessSentence p)) := TheoryTransport.sentence (source_uniqueness p)

theorem source_ZF_uniqueness {n} (p : Formula (n+3)) : Derives (Source.SetLanguage.ZF.at 0) (uniquenessSentence p) := source_ZF_replay (source_uniqueness p)

theorem native_uniqueness {n} (p : Formula (n+3)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence p)) :=
  native_replay (uniqueness_kernel_certificate p)
end PPAC.Migration.ObjectOrdinalRecursion
