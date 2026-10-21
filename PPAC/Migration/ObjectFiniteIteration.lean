import PPAC.Migration.FiniteIterationUniqueness

/-! 全部内部ω长度的实际有限轨迹存在和唯一性原核证书。 -/
namespace PPAC.Migration.ObjectFiniteIteration
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax IterationSyntax FiniteIterationSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.pairing ∨
  q = Source.SetLanguage.union ∨ q = Source.SetLanguage.foundation ∨ q = Source.SetLanguage.separation transitiveMatrix ∨
  q = Source.SetLanguage.separation IterationExistence.existenceMatrix ∨ q = Source.SetLanguage.separation subsetMatrix ∨
  q = Source.SetLanguage.separation agreementMatrix

def baseSentence : Source.Sentence := ((empty (0 : Fin 2)).imp (existsTrack 0 0 1)).close

def existenceSentence : Source.Sentence := ((omega (0 : Fin 3)).imp ((empty 1).imp
  (.all ((Formula.mem (Fin.last 3) (0 : Fin 3).castSucc).imp
    (existsTrack (Fin.last 3) (1 : Fin 3).castSucc (2 : Fin 3).castSucc))))).close

def uniquenessSentence : Source.Sentence := ((omega (0 : Fin 8)).imp ((empty 2).imp ((Formula.mem 1 0).imp
  ((witness 4 5 1 2 3).imp ((witness 6 7 1 2 3).imp ((Formula.equal 5 7).conj (.equal 4 6))))))).close

theorem source_base : Derives (assumptions.at 0) baseSentence := by
  apply close_derives
  apply Derives.impI
  have hp : Derives (assumptions.at 2) (Source.SetLanguage.pairing.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  have he : Derives (assumptions.at 2) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  exact IterationBaseExistence.exists_base 0 1 (add hp _) (add he _) (.hyp (Or.inl rfl))

theorem source_existence : Derives (assumptions.at 0) existenceSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 3) ((Source.SetLanguage.extensionality).rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have hp : Derives (assumptions.at 3) ((Source.SetLanguage.pairing).rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  have hu : Derives (assumptions.at 3) ((Source.SetLanguage.union).rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  have hfound : Derives (assumptions.at 3) ((Source.SetLanguage.foundation).rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  have htrans : Derives (assumptions.at 3) ((Source.SetLanguage.separation transitiveMatrix).rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
  have hexsep : Derives (assumptions.at 3) ((Source.SetLanguage.separation IterationExistence.existenceMatrix).rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), rfl⟩
  exact IterationExistence.all_exists 1 2 0 (add (add hp _) _) (add (add hu _) _) (add (add he _) _)
    (add (add hfound _) _) (add (add htrans _) _) (add (add hexsep _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_uniqueness : Derives (assumptions.at 0) uniquenessSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 8) ((Source.SetLanguage.extensionality).rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have htrans : Derives (assumptions.at 8) ((Source.SetLanguage.separation transitiveMatrix).rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
  have hsubset : Derives (assumptions.at 8) ((Source.SetLanguage.separation subsetMatrix).rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), rfl⟩
  have hagree : Derives (assumptions.at 8) ((Source.SetLanguage.separation agreementMatrix).rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))), rfl⟩
  exact FiniteIterationUniqueness.witness_equal 4 5 6 7 1 2 3 0
    (add (add (add (add (add he _) _) _) _) _) (add (add (add (add (add htrans _) _) _) _) _)
    (add (add (add (add (add hsubset _) _) _) _) _) (add (add (add (add (add hagree _) _) _) _) _)
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation transitiveMatrix, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation IterationExistence.existenceMatrix, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation subsetMatrix, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation agreementMatrix, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact ZFEquivalence.source_pairing
  · exact ZFEquivalence.source_union
  · exact ZFEquivalence.source_foundation
  · exact SeparationSyntax.source_separation transitiveMatrix
  · exact SeparationSyntax.source_separation IterationExistence.existenceMatrix
  · exact SeparationSyntax.source_separation subsetMatrix
  · exact SeparationSyntax.source_separation agreementMatrix

theorem base_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence baseSentence) := TheoryTransport.sentence source_base

theorem source_ZF_base : Derives (Source.SetLanguage.ZF.at 0) baseSentence := source_ZF_replay source_base

theorem native_base : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence baseSentence) :=
  native_replay base_kernel_certificate

theorem existence_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence existenceSentence) := TheoryTransport.sentence source_existence

theorem source_ZF_existence : Derives (Source.SetLanguage.ZF.at 0) existenceSentence := source_ZF_replay source_existence

theorem native_existence : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  native_replay existence_kernel_certificate

theorem uniqueness_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence uniquenessSentence) := TheoryTransport.sentence source_uniqueness

theorem source_ZF_uniqueness : Derives (Source.SetLanguage.ZF.at 0) uniquenessSentence := source_ZF_replay source_uniqueness

theorem native_uniqueness : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence uniquenessSentence) :=
  native_replay uniqueness_kernel_certificate
end PPAC.Migration.ObjectFiniteIteration
