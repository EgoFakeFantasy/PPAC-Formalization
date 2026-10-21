import PPAC.Migration.GraphInsertExistence

/-! 集合插入、源successor及一般新点图扩展的完整原核对象闭句。 -/
namespace PPAC.Migration.ObjectGraphInsert
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax InsertSyntax GraphInsertSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.pairing ∨
  q = Source.SetLanguage.union ∨ q = Source.SetLanguage.extensionality

def insertSentence : Source.Sentence := (insertExists (0 : Fin 2) 1).close

def successorSentence : Source.Sentence :=
  (Formula.ex (Source.SetLanguage.successor (Fin.last 1) (0 : Fin 1).castSucc)).close

def extensionSentence : Source.Sentence :=
  ((functionOn (0 : Fin 4) 1).imp ((Formula.mem 2 1).neg.imp (existsExtension 0 1 2 3))).close

def edgeLawSentence : Source.Sentence :=
  ((insert (0 : Fin 5) 1 2).imp ((ordered 2 3 4).imp (edgeLaw 0 1 3 4))).close

def uniquenessSentence : Source.Sentence :=
  ((witness (0 : Fin 10) 1 2 6 7 8 9).imp ((witness 3 4 5 6 7 8 9).imp
    ((Formula.equal 2 5).conj ((Formula.equal 1 4).conj (.equal 0 3))))).close

theorem source_uniqueness : Derives (assumptions.at 0) uniquenessSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 10) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr rfl), rfl⟩
  exact witness_unique 0 1 2 3 4 5 6 7 8 9 (add (add he _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_insert : Derives (assumptions.at 0) insertSentence := by
  apply close_derives
  exact InsertExistence.exists_insert 0 1 (.hyp ⟨_, Or.inl rfl, rfl⟩) (.hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩)

theorem source_successor : Derives (assumptions.at 0) successorSentence := by
  apply close_derives
  simp only [successor_original]
  exact InsertExistence.exists_insert 0 0 (.hyp ⟨_, Or.inl rfl, rfl⟩) (.hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩)

theorem source_extension : Derives (assumptions.at 0) extensionSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have hp : Derives (assumptions.at 4) (Source.SetLanguage.pairing.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have hu : Derives (assumptions.at 4) (Source.SetLanguage.union.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  have he : Derives (assumptions.at 4) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr rfl), rfl⟩
  exact GraphInsertExistence.exists_extension 0 1 2 3 (add (add hp _) _) (add (add hu _) _) (add (add he _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_edge_law : Derives (assumptions.at 0) edgeLawSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 5) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inr (Or.inr rfl), rfl⟩
  exact all_edges 0 1 2 3 4 (add (add he _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) :
    Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl | rfl
  · exact ZFEquivalence.source_pairing
  · exact ZFEquivalence.source_union
  · exact ZFEquivalence.source_extensionality

theorem insert_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence insertSentence) := TheoryTransport.sentence source_insert

theorem source_ZF_insert : Derives (Source.SetLanguage.ZF.at 0) insertSentence := source_ZF_replay source_insert

theorem native_insert : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence insertSentence) :=
  native_replay insert_kernel_certificate

theorem successor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence successorSentence) := TheoryTransport.sentence source_successor

theorem source_ZF_successor : Derives (Source.SetLanguage.ZF.at 0) successorSentence := source_ZF_replay source_successor

theorem native_successor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence successorSentence) :=
  native_replay successor_kernel_certificate

theorem extension_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence extensionSentence) := TheoryTransport.sentence source_extension

theorem source_ZF_extension : Derives (Source.SetLanguage.ZF.at 0) extensionSentence := source_ZF_replay source_extension

theorem native_extension : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence extensionSentence) :=
  native_replay extension_kernel_certificate

theorem edge_law_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence edgeLawSentence) := TheoryTransport.sentence source_edge_law

theorem source_ZF_edge_law : Derives (Source.SetLanguage.ZF.at 0) edgeLawSentence := source_ZF_replay source_edge_law

theorem native_edge_law : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence edgeLawSentence) :=
  native_replay edge_law_kernel_certificate
theorem uniqueness_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence uniquenessSentence) := TheoryTransport.sentence source_uniqueness

theorem source_ZF_uniqueness : Derives (Source.SetLanguage.ZF.at 0) uniquenessSentence := source_ZF_replay source_uniqueness

theorem native_uniqueness : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence uniquenessSentence) := native_replay uniqueness_kernel_certificate
end PPAC.Migration.ObjectGraphInsert
