import PPAC.Migration.RestrictionExistence

/-! 任意对象图限制、唯一性与组合律的原核全量词闭句。 -/
namespace PPAC.Migration.ObjectRestriction
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax RestrictionSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.separation matrix

def setSentence : Source.Sentence := (restrictExists (0 : Fin 2) 1).close

def functionSentence : Source.Sentence :=
  ((functionOn (0 : Fin 3) 1).imp ((subset 2 1).imp (existsRestriction 0 2))).close

def edgeSentence : Source.Sentence := ((restrict (0 : Fin 3) 1 2).imp (edgeLaw 0 1 2)).close

def uniqueSentence : Source.Sentence :=
  ((restrict (0 : Fin 4) 2 3).imp ((restrict 1 2 3).imp (.equal 0 1))).close

def identitySentence : Source.Sentence :=
  ((functionOn (1 : Fin 3) 2).imp ((restrict 0 1 2).imp (.equal 0 1))).close

def composeSentence : Source.Sentence :=
  ((subset (4 : Fin 5) 3).imp ((restrict 1 2 3).imp ((restrict 0 1 4).imp (restrict 0 2 4)))).close

theorem source_set : Derives (assumptions.at 0) setSentence := by
  apply close_derives
  exact exists_restrict 0 1 (.hyp ⟨_, Or.inr rfl, rfl⟩)

theorem source_function : Derives (assumptions.at 0) functionSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Derives (assumptions.at 3) ((Source.SetLanguage.separation matrix).rename Fin.elim0) := .hyp ⟨_, Or.inr rfl, rfl⟩
  exact RestrictionExistence.exists_function_restriction 0 1 2 (add (add hs _) _) (add (add he _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_edge : Derives (assumptions.at 0) edgeSentence := by
  apply close_derives
  apply Derives.impI
  have he : Derives (assumptions.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  exact RestrictionEdges.all_edges 0 1 2 (add he _) (.hyp (Or.inl rfl))

theorem source_unique : Derives (assumptions.at 0) uniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 4) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  exact RestrictionAlgebra.unique 0 1 2 3 (add (add he _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_identity : Derives (assumptions.at 0) identitySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  exact RestrictionAlgebra.identity 0 1 2 (add (add he _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_compose : Derives (assumptions.at 0) composeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact RestrictionAlgebra.compose 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) :
    Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation matrix, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact SeparationSyntax.source_separation matrix

theorem set_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence setSentence) := TheoryTransport.sentence source_set

theorem source_ZF_set : Derives (Source.SetLanguage.ZF.at 0) setSentence := source_ZF_replay source_set

theorem native_set : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence setSentence) :=
  native_replay set_kernel_certificate

theorem function_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence functionSentence) := TheoryTransport.sentence source_function

theorem source_ZF_function : Derives (Source.SetLanguage.ZF.at 0) functionSentence := source_ZF_replay source_function

theorem native_function : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence functionSentence) :=
  native_replay function_kernel_certificate

theorem edge_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence edgeSentence) := TheoryTransport.sentence source_edge

theorem source_ZF_edge : Derives (Source.SetLanguage.ZF.at 0) edgeSentence := source_ZF_replay source_edge

theorem native_edge : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence edgeSentence) :=
  native_replay edge_kernel_certificate

theorem unique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence uniqueSentence) := TheoryTransport.sentence source_unique

theorem source_ZF_unique : Derives (Source.SetLanguage.ZF.at 0) uniqueSentence := source_ZF_replay source_unique

theorem native_unique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence uniqueSentence) :=
  native_replay unique_kernel_certificate

theorem identity_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence identitySentence) := TheoryTransport.sentence source_identity

theorem source_ZF_identity : Derives (Source.SetLanguage.ZF.at 0) identitySentence := source_ZF_replay source_identity

theorem native_identity : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence identitySentence) :=
  native_replay identity_kernel_certificate

theorem compose_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence composeSentence) := TheoryTransport.sentence source_compose

theorem source_ZF_compose : Derives (Source.SetLanguage.ZF.at 0) composeSentence := source_ZF_replay source_compose

theorem native_compose : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence composeSentence) :=
  native_replay compose_kernel_certificate
end PPAC.Migration.ObjectRestriction
