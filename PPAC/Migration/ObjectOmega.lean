import PPAC.Migration.OmegaInduction

/-! 实际最小归纳集ω的存在、唯一性和完整对象成员刻画。 -/
namespace PPAC.Migration.ObjectOmega
open Source SourceAlgebra SourceLogic OmegaSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.infinity ∨
  q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.separation matrix

def uniqueSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((omega 1).imp (.equal 0 1))).close

def characterizationSentence : Source.Sentence :=
  ((omega (0 : Fin 1)).imp (.all ((Formula.mem (Fin.last 1) (0 : Fin 1).castSucc).iff
    (universal (Fin.last 1))))).close

theorem source_existence : Derives (assumptions.at 0) omegaExists := by
  have he := OmegaExistence.exists_omega (Γ := assumptions.at 0)
    (Derives.hyp ⟨_, Or.inl rfl, rfl⟩) (Derives.hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩)
    (Derives.hyp ⟨_, Or.inr (Or.inr rfl), rfl⟩)
  have hId : (Fin.elim0 : Fin 0 → Fin 0) = id := by funext i; exact Fin.elim0 i
  simpa only [hId, Reverse.source_rename_id] using he

theorem source_unique : Derives (assumptions.at 0) uniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 2) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  exact OmegaAlgebra.unique 0 1 (add (add he _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_characterization : Derives (assumptions.at 0) characterizationSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.allI
  have hw : Derives (Context.image Formula.raise (Context.add (omega (0 : Fin 1)) (assumptions.at 1)))
      (omega (0 : Fin 1).castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.hyp (Γ := Context.add (omega (0 : Fin 1)) (assumptions.at 1)) (Or.inl rfl))
  exact OmegaAlgebra.membership_iff (0 : Fin 1).castSucc (Fin.last 1) hw

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) :
    Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.infinity, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation matrix, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl | rfl
  · exact ZFEquivalence.source_infinity
  · exact ZFEquivalence.source_extensionality
  · exact SeparationSyntax.source_separation matrix

theorem existence_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence omegaExists) := TheoryTransport.sentence source_existence

theorem source_ZF_existence : Derives (Source.SetLanguage.ZF.at 0) omegaExists := source_ZF_replay source_existence

theorem native_existence : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence omegaExists) :=
  native_replay existence_kernel_certificate

theorem unique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence uniqueSentence) := TheoryTransport.sentence source_unique

theorem source_ZF_unique : Derives (Source.SetLanguage.ZF.at 0) uniqueSentence := source_ZF_replay source_unique

theorem native_unique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence uniqueSentence) :=
  native_replay unique_kernel_certificate

theorem characterization_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence characterizationSentence) := TheoryTransport.sentence source_characterization

theorem source_ZF_characterization : Derives (Source.SetLanguage.ZF.at 0) characterizationSentence := source_ZF_replay source_characterization

theorem native_characterization : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence characterizationSentence) :=
  native_replay characterization_kernel_certificate
end PPAC.Migration.ObjectOmega
