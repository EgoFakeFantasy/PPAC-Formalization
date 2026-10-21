import PPAC.Migration.GraphFamilyEmpty

/-! 任意内部相容图集合族并图、实际定义域与唯一性的原核对象定理。 -/
namespace PPAC.Migration.ObjectGraphFamily
open Source SourceAlgebra SourceLogic GraphSyntax InsertSyntax GraphDomainSyntax GraphFamilySyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.union ∨
  q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.separation GraphDomainSyntax.matrix

def domainSentence : Source.Sentence := (domainExists (0 : Fin 1)).close

def domainUniqueSentence : Source.Sentence :=
  ((domain (0 : Fin 3) 2).imp ((domain 1 2).imp (.equal 0 1))).close

def unionSentence : Source.Sentence :=
  ((graphs (0 : Fin 1)).imp ((compatible 0).imp (existsUnion 0))).close

def uniqueSentence : Source.Sentence :=
  ((witness (0 : Fin 5) 1 4).imp ((witness 2 3 4).imp ((Formula.equal 0 2).conj (.equal 1 3)))).close

def edgeSentence : Source.Sentence := ((unionOf (0 : Fin 2) 1).imp (edgeLaw 0 1)).close

def emptySentence : Source.Sentence := ((Source.SetLanguage.empty (0 : Fin 1)).imp (existsUnion 0)).close

theorem source_domain : Derives (assumptions.at 0) domainSentence := by
  apply close_derives
  exact GraphDomainExistence.exists_domain 0 (.hyp ⟨_, Or.inl rfl, rfl⟩) (.hyp ⟨_, Or.inr (Or.inr rfl), rfl⟩)

theorem source_domain_unique : Derives (assumptions.at 0) domainUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  exact GraphDomainAlgebra.unique 0 1 2 (add (add he _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_union : Derives (assumptions.at 0) unionSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have hu : Derives (assumptions.at 1) (Source.SetLanguage.union.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Derives (assumptions.at 1) ((Source.SetLanguage.separation GraphDomainSyntax.matrix).rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr rfl), rfl⟩
  exact GraphFamilyExistence.exists_union 0 (add (add hu _) _) (add (add hs _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_unique : Derives (assumptions.at 0) uniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 5) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  exact GraphFamilyExistence.witness_unique 0 1 2 3 4 (add (add he _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_edge : Derives (assumptions.at 0) edgeSentence := by
  apply close_derives
  apply Derives.impI
  exact GraphFamilyEdges.all_edges 0 1 (.hyp (Or.inl rfl))

theorem source_empty : Derives (assumptions.at 0) emptySentence := by
  apply close_derives
  apply Derives.impI
  have hu : Derives (assumptions.at 1) (Source.SetLanguage.union.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Derives (assumptions.at 1) ((Source.SetLanguage.separation GraphDomainSyntax.matrix).rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr rfl), rfl⟩
  exact GraphFamilyExistence.exists_union 0 (add hu _) (add hs _)
    (GraphFamilyEmpty.graphs_of_empty 0 (.hyp (Or.inl rfl)))
    (GraphFamilyEmpty.compatible_of_empty 0 (.hyp (Or.inl rfl)))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) :
    Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation GraphDomainSyntax.matrix, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl | rfl
  · exact ZFEquivalence.source_union
  · exact ZFEquivalence.source_extensionality
  · exact SeparationSyntax.source_separation GraphDomainSyntax.matrix

theorem domain_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence domainSentence) := TheoryTransport.sentence source_domain

theorem source_ZF_domain : Derives (Source.SetLanguage.ZF.at 0) domainSentence := source_ZF_replay source_domain

theorem native_domain : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence domainSentence) :=
  native_replay domain_kernel_certificate

theorem domain_unique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence domainUniqueSentence) := TheoryTransport.sentence source_domain_unique

theorem source_ZF_domain_unique : Derives (Source.SetLanguage.ZF.at 0) domainUniqueSentence := source_ZF_replay source_domain_unique

theorem native_domain_unique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence domainUniqueSentence) :=
  native_replay domain_unique_kernel_certificate

theorem union_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence unionSentence) := TheoryTransport.sentence source_union

theorem source_ZF_union : Derives (Source.SetLanguage.ZF.at 0) unionSentence := source_ZF_replay source_union

theorem native_union : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence unionSentence) :=
  native_replay union_kernel_certificate

theorem unique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence uniqueSentence) := TheoryTransport.sentence source_unique

theorem source_ZF_unique : Derives (Source.SetLanguage.ZF.at 0) uniqueSentence := source_ZF_replay source_unique

theorem native_unique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence uniqueSentence) :=
  native_replay unique_kernel_certificate

theorem edge_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence edgeSentence) := TheoryTransport.sentence source_edge

theorem source_ZF_edge : Derives (Source.SetLanguage.ZF.at 0) edgeSentence := source_ZF_replay source_edge

theorem native_edge : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence edgeSentence) :=
  native_replay edge_kernel_certificate

theorem empty_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence emptySentence) := TheoryTransport.sentence source_empty

theorem source_ZF_empty : Derives (Source.SetLanguage.ZF.at 0) emptySentence := source_ZF_replay source_empty

theorem native_empty : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence emptySentence) :=
  native_replay empty_kernel_certificate
end PPAC.Migration.ObjectGraphFamily
