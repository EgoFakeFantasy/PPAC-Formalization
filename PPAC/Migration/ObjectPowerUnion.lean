import PPAC.Migration.PowerUnionOperation

/-! 四句有限原理论中的实际幂集并算子：总性和单值性均已实际证明。 -/
namespace PPAC.Migration.ObjectPowerUnion
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalSyntax PowerUnionSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.powerSet ∨
  q = Source.SetLanguage.union ∨ q = Source.SetLanguage.replacement PowerValueSyntax.matrix

def rangeSentence : Source.Sentence := ((functionOn (1 : Fin 2) 0).imp (PowerValueSyntax.rangeExists 0 1)).close

def operationSentence : Source.Sentence := ((functionOn (1 : Fin 2) 0).imp (existsOperation 0 1)).close

def totalSentence : Source.Sentence := OrdinalRecursionTotal.total matrix (id : Fin 0 → Fin 0)

def deterministicSentence : Source.Sentence := OrdinalRecursionDeterminism.deterministic matrix (id : Fin 0 → Fin 0)

theorem ext_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩

theorem power_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.powerSet.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩

theorem union_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.union.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩

theorem replacement_at (m : Nat) : Derives (assumptions.at m)
    ((Source.SetLanguage.replacement PowerValueSyntax.matrix).rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩

theorem source_range : Derives (assumptions.at 0) rangeSentence := by
  apply close_derives
  apply Derives.impI
  exact PowerValueCollection.exists_range 1 0 (add (ext_at 2) _) (add (power_at 2) _) (add (replacement_at 2) _) (.hyp (Or.inl rfl))

theorem source_operation : Derives (assumptions.at 0) operationSentence := by
  apply close_derives
  apply Derives.impI
  exact PowerUnionOperation.exists_operation 0 1 (add (ext_at 2) _) (add (power_at 2) _)
    (add (replacement_at 2) _) (add (union_at 2) _) (.hyp (Or.inl rfl))

theorem source_total : Derives (assumptions.at 0) totalSentence := by
  have hAll : Derives (assumptions.at 0) (.all (.all
      (((ordinal (0 : Fin 2)).conj (functionOn 1 0)).imp (existsOperation 0 1)))) := by
    apply Derives.allI
    apply Derives.allI
    rw [theory_at_raise, theory_at_raise]
    apply Derives.impI
    exact PowerUnionOperation.exists_operation 0 1 (add (ext_at 2) _) (add (power_at 2) _)
      (add (replacement_at 2) _) (add (union_at 2) _) (.conjR (.hyp (Or.inl rfl)))
  simp only [totalSentence, OrdinalRecursionTotal.total, OrdinalRecursionTotal.hasValue, matrix_operator]
  exact hAll

theorem source_deterministic : Derives (assumptions.at 0) deterministicSentence := by
  have hAll : Derives (assumptions.at 0) (.all (.all
      (((ordinal (0 : Fin 2)).conj (functionOn 1 0)).imp (.all (.all
        ((operation (0 : Fin 2).castSucc.castSucc (1 : Fin 2).castSucc.castSucc (Fin.last 2).castSucc).imp
          ((operation (0 : Fin 2).castSucc.castSucc (1 : Fin 2).castSucc.castSucc (Fin.last 3)).imp
            (.equal (Fin.last 2).castSucc (Fin.last 3))))))))) := by
    apply Derives.allI
    apply Derives.allI
    rw [theory_at_raise, theory_at_raise]
    have he := ext_at 2
    apply Derives.impI
    let V := (ordinal (0 : Fin 2)).conj (functionOn 1 0)
    have heV := add he V
    apply Derives.allI
    apply Derives.allI
    have he' : Derives (Context.image Formula.raise (Context.image Formula.raise (Context.add V (assumptions.at 2))))
        (Source.SetLanguage.extensionality.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc heV)
    apply Derives.impI
    apply Derives.impI
    exact PowerUnionOperation.unique (0 : Fin 2).castSucc.castSucc (1 : Fin 2).castSucc.castSucc
      (Fin.last 2).castSucc (Fin.last 3) (add (add he' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
  simp only [deterministicSentence, OrdinalRecursionDeterminism.deterministic, OrdinalRecursionDeterminism.functional, matrix_operator]
  exact hAll

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.powerSet, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.replacement PowerValueSyntax.matrix, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact ZFEquivalence.source_powerSet
  · exact ZFEquivalence.source_union
  · exact ReplacementFromCollection.native_replacement PowerValueSyntax.matrix

theorem range_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence rangeSentence) := TheoryTransport.sentence source_range

theorem source_ZF_range : Derives (Source.SetLanguage.ZF.at 0) rangeSentence := source_ZF_replay source_range

theorem native_range : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rangeSentence) := native_replay range_kernel_certificate

theorem operation_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence operationSentence) := TheoryTransport.sentence source_operation

theorem source_ZF_operation : Derives (Source.SetLanguage.ZF.at 0) operationSentence := source_ZF_replay source_operation

theorem native_operation : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence operationSentence) := native_replay operation_kernel_certificate

theorem total_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence totalSentence) := TheoryTransport.sentence source_total

theorem source_ZF_total : Derives (Source.SetLanguage.ZF.at 0) totalSentence := source_ZF_replay source_total

theorem native_total : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence totalSentence) := native_replay total_kernel_certificate

theorem deterministic_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence deterministicSentence) := TheoryTransport.sentence source_deterministic

theorem source_ZF_deterministic : Derives (Source.SetLanguage.ZF.at 0) deterministicSentence := source_ZF_replay source_deterministic

theorem native_deterministic : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence deterministicSentence) := native_replay deterministic_kernel_certificate
end PPAC.Migration.ObjectPowerUnion
