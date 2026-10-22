import PPAC.Migration.Internal.SyntaxRenameAtomicBase

/-! 四类原子实际唯一输出和六内部参数归纳基础情形的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxRenameAtomic
open Source SourceAlgebra SourceLogic OmegaSyntax

def graphCasesSentence {m} (w R S r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxRenameRecursiveSyntax.localRename w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q)))).close

theorem source_graphCases {m} (w R S r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphCasesSentence w R S r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inl rfl)
  exact SyntaxRenameActualGraphs.at_graphs hZ w R S r s a b c d n q h0 h1

theorem graphCases_kernel_certificate {m} (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphCasesSentence w R S r s a b c d n q)) := TheoryTransport.sentence (source_graphCases w R S r s a b c d n q)

theorem native_graphCases {m} (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphCasesSentence w R S r s a b c d n q)) := ZFReplay.replay (graphCases_kernel_certificate w R S r s a b c d n q)

def casesFromJudgmentSentence {m} (w R S r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q))))).close

theorem source_casesFromJudgment {m} (w R S r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (casesFromJudgmentSentence w R S r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameActualGraphs.cases_of_renamed hZ w R S r s a b c d n q h0 h1 h2 h3

theorem casesFromJudgment_kernel_certificate {m} (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (casesFromJudgmentSentence w R S r s a b c d n q)) := TheoryTransport.sentence (source_casesFromJudgment w R S r s a b c d n q)

theorem native_casesFromJudgment {m} (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (casesFromJudgmentSentence w R S r s a b c d n q)) := ZFReplay.replay (casesFromJudgment_kernel_certificate w R S r s a b c d n q)

def atomicFromJudgmentSentence {m} (kind : Fin 4) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxNodeSyntax.constructor arity kind.val w xs n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp (SyntaxRenameAtomicCases.atomicCase kind w r s a b c d n q)))))).close

theorem source_atomicFromJudgment {m} (kind : Fin 4) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atomicFromJudgmentSentence kind arity w R S r s a b c d n q xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxNodeSyntax.constructor arity kind.val w xs n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxNodeSyntax.constructor arity kind.val w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameActualGraphs.atomic_of_renamed hZ kind arity w R S r s a b c d n q xs h0 h1 h2 h3 h4

theorem atomicFromJudgment_kernel_certificate {m} (kind : Fin 4) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atomicFromJudgmentSentence kind arity w R S r s a b c d n q xs)) := TheoryTransport.sentence (source_atomicFromJudgment kind arity w R S r s a b c d n q xs)

theorem native_atomicFromJudgment {m} (kind : Fin 4) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atomicFromJudgmentSentence kind arity w R S r s a b c d n q xs)) := ZFReplay.replay (atomicFromJudgment_kernel_certificate kind arity w R S r s a b c d n q xs)

def introFromCasesSentence {m} (w R S r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((FormulaCodeSyntax.formulaCode w q c d).imp ((SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q).imp (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))))))).close

theorem source_introFromCases {m} (w R S r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (introFromCasesSentence w R S r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q) (Context.add (FormulaCodeSyntax.formulaCode w q c d) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (FormulaCodeSyntax.formulaCode w q c d) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameActualGraphs.intro_from_cases hZ w R S r s a b c d n q h0 h1 h2 h3 h4 h5

theorem introFromCases_kernel_certificate {m} (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (introFromCasesSentence w R S r s a b c d n q)) := TheoryTransport.sentence (source_introFromCases w R S r s a b c d n q)

theorem native_introFromCases {m} (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (introFromCasesSentence w R S r s a b c d n q)) := ZFReplay.replay (introFromCases_kernel_certificate w R S r s a b c d n q)

def equalDataUniqueSentence {m} (w r s a b c d n q v x y X Y u z U V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameAtomSyntax.equalityData w r s a b c d n q x y X Y).imp ((SyntaxRenameAtomSyntax.equalityData w r s a b c d n v u z U V).imp (Formula.equal q v)))).close

theorem source_equalDataUnique {m} (w r s a b c d n q v x y X Y u z U V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalDataUniqueSentence w r s a b c d n q v x y X Y u z U V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameAtomSyntax.equalityData w r s a b c d n v u z U V) (Context.add (SyntaxRenameAtomSyntax.equalityData w r s a b c d n q x y X Y) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameAtomSyntax.equalityData w r s a b c d n q x y X Y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameAtomSyntax.equalityData w r s a b c d n v u z U V) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomUnique.equality_data_unique hZ w r s a b c d n q v x y X Y u z U V h0 h1 h2

theorem equalDataUnique_kernel_certificate {m} (w r s a b c d n q v x y X Y u z U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalDataUniqueSentence w r s a b c d n q v x y X Y u z U V)) := TheoryTransport.sentence (source_equalDataUnique w r s a b c d n q v x y X Y u z U V)

theorem native_equalDataUnique {m} (w r s a b c d n q v x y X Y u z U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalDataUniqueSentence w r s a b c d n q v x y X Y u z U V)) := ZFReplay.replay (equalDataUnique_kernel_certificate w r s a b c d n q v x y X Y u z U V)

def equalRelationUniqueSentence {m} (w r s a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp ((SyntaxRenameAtomSyntax.equality w r s a b c d n v).imp (Formula.equal q v)))).close

theorem source_equalRelationUnique {m} (w r s a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalRelationUniqueSentence w r s a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameAtomSyntax.equality w r s a b c d n v) (Context.add (SyntaxRenameAtomSyntax.equality w r s a b c d n q) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameAtomSyntax.equality w r s a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameAtomSyntax.equality w r s a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomUnique.equality_unique hZ w r s a b c d n q v h0 h1 h2

theorem equalRelationUnique_kernel_certificate {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalRelationUniqueSentence w r s a b c d n q v)) := TheoryTransport.sentence (source_equalRelationUnique w r s a b c d n q v)

theorem native_equalRelationUnique {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalRelationUniqueSentence w r s a b c d n q v)) := ZFReplay.replay (equalRelationUnique_kernel_certificate w r s a b c d n q v)

def equalAtOutputsSentence {m} (w R S r s a b c d n x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxRenameTermSyntax.renamed w r s a b c d x X).imp ((SyntaxRenameTermSyntax.renamed w r s a b c d y Y).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n)))))))).close

theorem source_equalAtOutputs {m} (w R S r s a b c d n x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalAtOutputsSentence w R S r s a b c d n x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.renamed w r s a b c d y Y) (Context.add (SyntaxRenameTermSyntax.renamed w r s a b c d x X) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxRenameTermSyntax.renamed w r s a b c d x X) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxRenameTermSyntax.renamed w r s a b c d y Y) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomConstruct.equality_at_outputs hZ w R S r s a b c d n x y X Y h0 h1 h2 h3 h4 h5 h6

theorem equalAtOutputs_kernel_certificate {m} (w R S r s a b c d n x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalAtOutputsSentence w R S r s a b c d n x y X Y)) := TheoryTransport.sentence (source_equalAtOutputs w R S r s a b c d n x y X Y)

theorem native_equalAtOutputs {m} (w R S r s a b c d n x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalAtOutputsSentence w R S r s a b c d n x y X Y)) := ZFReplay.replay (equalAtOutputs_kernel_certificate w R S r s a b c d n x y X Y)

def equalExistsAtGraphsSentence {m} (w R S r s a b c d n x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.equalCode w x y n).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n)))))).close

theorem source_equalExistsAtGraphs {m} (w R S r s a b c d n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalExistsAtGraphsSentence w R S r s a b c d n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomConstruct.equality_exists_at_graphs hZ w R S r s a b c d n x y h0 h1 h2 h3 h4

theorem equalExistsAtGraphs_kernel_certificate {m} (w R S r s a b c d n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalExistsAtGraphsSentence w R S r s a b c d n x y)) := TheoryTransport.sentence (source_equalExistsAtGraphs w R S r s a b c d n x y)

theorem native_equalExistsAtGraphs {m} (w R S r s a b c d n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalExistsAtGraphsSentence w R S r s a b c d n x y)) := ZFReplay.replay (equalExistsAtGraphs_kernel_certificate w R S r s a b c d n x y)

def equalUniqueAtGraphsSentence {m} (w R S r s a b c d n q v x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v).imp (Formula.equal q v))))))).close

theorem source_equalUniqueAtGraphs {m} (w R S r s a b c d n q v x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalUniqueAtGraphsSentence w R S r s a b c d n q v x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomOutput.equality_unique_at_graphs hZ w R S r s a b c d n q v x y h0 h1 h2 h3 h4 h5

theorem equalUniqueAtGraphs_kernel_certificate {m} (w R S r s a b c d n q v x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalUniqueAtGraphsSentence w R S r s a b c d n q v x y)) := TheoryTransport.sentence (source_equalUniqueAtGraphs w R S r s a b c d n q v x y)

theorem native_equalUniqueAtGraphs {m} (w R S r s a b c d n q v x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalUniqueAtGraphsSentence w R S r s a b c d n q v x y)) := ZFReplay.replay (equalUniqueAtGraphs_kernel_certificate w R S r s a b c d n q v x y)

def equalFiberAtGraphsSentence {m} (w R S r s a b c d n x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.equalCode w x y n).imp (SyntaxRenameOutputSyntax.fiber w R S a b c d n)))))).close

theorem source_equalFiberAtGraphs {m} (w R S r s a b c d n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalFiberAtGraphsSentence w R S r s a b c d n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomOutput.equality_fiber_at_graphs hZ w R S r s a b c d n x y h0 h1 h2 h3 h4

theorem equalFiberAtGraphs_kernel_certificate {m} (w R S r s a b c d n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalFiberAtGraphsSentence w R S r s a b c d n x y)) := TheoryTransport.sentence (source_equalFiberAtGraphs w R S r s a b c d n x y)

theorem native_equalFiberAtGraphs {m} (w R S r s a b c d n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalFiberAtGraphsSentence w R S r s a b c d n x y)) := ZFReplay.replay (equalFiberAtGraphs_kernel_certificate w R S r s a b c d n x y)

def equalFiberSentence {m} (w R S a b c d n x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxAtomSyntax.equalCode w x y n).imp (SyntaxRenameOutputSyntax.fiber w R S a b c d n)))).close

theorem source_equalFiber {m} (w R S a b c d n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalFiberSentence w R S a b c d n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomOutput.equality_fiber hZ w R S a b c d n x y h0 h1 h2

theorem equalFiber_kernel_certificate {m} (w R S a b c d n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalFiberSentence w R S a b c d n x y)) := TheoryTransport.sentence (source_equalFiber w R S a b c d n x y)

theorem native_equalFiber {m} (w R S a b c d n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalFiberSentence w R S a b c d n x y)) := ZFReplay.replay (equalFiber_kernel_certificate w R S a b c d n x y)

def equalAllParametersSentence {m} (w n x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.equalCode w x y n).imp (SyntaxRenameOutputSyntax.property w n))).close

theorem source_equalAllParameters {m} (w n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalAllParametersSentence w n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomOutput.equality_property_all_parameters hZ w n x y h0 h1

theorem equalAllParameters_kernel_certificate {m} (w n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalAllParametersSentence w n x y)) := TheoryTransport.sentence (source_equalAllParameters w n x y)

theorem native_equalAllParameters {m} (w n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalAllParametersSentence w n x y)) := ZFReplay.replay (equalAllParameters_kernel_certificate w n x y)

def equalBasePropertySentence {m} (w a b n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.equality w a b n).imp (SyntaxRenameOutputSyntax.property w n))).close

theorem source_equalBaseProperty {m} (w a b n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalBasePropertySentence w a b n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equality w a b n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.equality w a b n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomicBase.equality_property hZ w a b n h0 h1

theorem equalBaseProperty_kernel_certificate {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalBasePropertySentence w a b n)) := TheoryTransport.sentence (source_equalBaseProperty w a b n)

theorem native_equalBaseProperty {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalBasePropertySentence w a b n)) := ZFReplay.replay (equalBaseProperty_kernel_certificate w a b n)

def memberDataUniqueSentence {m} (w r s a b c d n q v z x y X Y j u t U V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameAtomSyntax.membershipData w r s a b c d n q z x y X Y).imp ((SyntaxRenameAtomSyntax.membershipData w r s a b c d n v j u t U V).imp (Formula.equal q v)))).close

theorem source_memberDataUnique {m} (w r s a b c d n q v z x y X Y j u t U V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberDataUniqueSentence w r s a b c d n q v z x y X Y j u t U V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameAtomSyntax.membershipData w r s a b c d n v j u t U V) (Context.add (SyntaxRenameAtomSyntax.membershipData w r s a b c d n q z x y X Y) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameAtomSyntax.membershipData w r s a b c d n q z x y X Y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameAtomSyntax.membershipData w r s a b c d n v j u t U V) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomUnique.membership_data_unique hZ w r s a b c d n q v z x y X Y j u t U V h0 h1 h2

theorem memberDataUnique_kernel_certificate {m} (w r s a b c d n q v z x y X Y j u t U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberDataUniqueSentence w r s a b c d n q v z x y X Y j u t U V)) := TheoryTransport.sentence (source_memberDataUnique w r s a b c d n q v z x y X Y j u t U V)

theorem native_memberDataUnique {m} (w r s a b c d n q v z x y X Y j u t U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberDataUniqueSentence w r s a b c d n q v z x y X Y j u t U V)) := ZFReplay.replay (memberDataUnique_kernel_certificate w r s a b c d n q v z x y X Y j u t U V)

def memberRelationUniqueSentence {m} (w r s a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp ((SyntaxRenameAtomSyntax.membership w r s a b c d n v).imp (Formula.equal q v)))).close

theorem source_memberRelationUnique {m} (w r s a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberRelationUniqueSentence w r s a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameAtomSyntax.membership w r s a b c d n v) (Context.add (SyntaxRenameAtomSyntax.membership w r s a b c d n q) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameAtomSyntax.membership w r s a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameAtomSyntax.membership w r s a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomUnique.membership_unique hZ w r s a b c d n q v h0 h1 h2

theorem memberRelationUnique_kernel_certificate {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberRelationUniqueSentence w r s a b c d n q v)) := TheoryTransport.sentence (source_memberRelationUnique w r s a b c d n q v)

theorem native_memberRelationUnique {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberRelationUniqueSentence w r s a b c d n q v)) := ZFReplay.replay (memberRelationUnique_kernel_certificate w r s a b c d n q v)

def memberAtOutputsSentence {m} (w R S r s a b c d n z x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxRenameTermSyntax.renamed w r s a b c d x X).imp ((SyntaxRenameTermSyntax.renamed w r s a b c d y Y).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n)))))))).close

theorem source_memberAtOutputs {m} (w R S r s a b c d n z x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberAtOutputsSentence w R S r s a b c d n z x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.renamed w r s a b c d y Y) (Context.add (SyntaxRenameTermSyntax.renamed w r s a b c d x X) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxRenameTermSyntax.renamed w r s a b c d x X) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxRenameTermSyntax.renamed w r s a b c d y Y) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomConstruct.membership_at_outputs hZ w R S r s a b c d n z x y X Y h0 h1 h2 h3 h4 h5 h6

theorem memberAtOutputs_kernel_certificate {m} (w R S r s a b c d n z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberAtOutputsSentence w R S r s a b c d n z x y X Y)) := TheoryTransport.sentence (source_memberAtOutputs w R S r s a b c d n z x y X Y)

theorem native_memberAtOutputs {m} (w R S r s a b c d n z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberAtOutputsSentence w R S r s a b c d n z x y X Y)) := ZFReplay.replay (memberAtOutputs_kernel_certificate w R S r s a b c d n z x y X Y)

def memberExistsAtGraphsSentence {m} (w R S r s a b c d n z x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n)))))).close

theorem source_memberExistsAtGraphs {m} (w R S r s a b c d n z x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberExistsAtGraphsSentence w R S r s a b c d n z x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomConstruct.membership_exists_at_graphs hZ w R S r s a b c d n z x y h0 h1 h2 h3 h4

theorem memberExistsAtGraphs_kernel_certificate {m} (w R S r s a b c d n z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberExistsAtGraphsSentence w R S r s a b c d n z x y)) := TheoryTransport.sentence (source_memberExistsAtGraphs w R S r s a b c d n z x y)

theorem native_memberExistsAtGraphs {m} (w R S r s a b c d n z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberExistsAtGraphsSentence w R S r s a b c d n z x y)) := ZFReplay.replay (memberExistsAtGraphs_kernel_certificate w R S r s a b c d n z x y)

def memberUniqueAtGraphsSentence {m} (w R S r s a b c d n q v z x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v).imp (Formula.equal q v))))))).close

theorem source_memberUniqueAtGraphs {m} (w R S r s a b c d n q v z x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberUniqueAtGraphsSentence w R S r s a b c d n q v z x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomOutput.membership_unique_at_graphs hZ w R S r s a b c d n q v z x y h0 h1 h2 h3 h4 h5

theorem memberUniqueAtGraphs_kernel_certificate {m} (w R S r s a b c d n q v z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberUniqueAtGraphsSentence w R S r s a b c d n q v z x y)) := TheoryTransport.sentence (source_memberUniqueAtGraphs w R S r s a b c d n q v z x y)

theorem native_memberUniqueAtGraphs {m} (w R S r s a b c d n q v z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberUniqueAtGraphsSentence w R S r s a b c d n q v z x y)) := ZFReplay.replay (memberUniqueAtGraphs_kernel_certificate w R S r s a b c d n q v z x y)

def memberFiberAtGraphsSentence {m} (w R S r s a b c d n z x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp (SyntaxRenameOutputSyntax.fiber w R S a b c d n)))))).close

theorem source_memberFiberAtGraphs {m} (w R S r s a b c d n z x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberFiberAtGraphsSentence w R S r s a b c d n z x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomOutput.membership_fiber_at_graphs hZ w R S r s a b c d n z x y h0 h1 h2 h3 h4

theorem memberFiberAtGraphs_kernel_certificate {m} (w R S r s a b c d n z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberFiberAtGraphsSentence w R S r s a b c d n z x y)) := TheoryTransport.sentence (source_memberFiberAtGraphs w R S r s a b c d n z x y)

theorem native_memberFiberAtGraphs {m} (w R S r s a b c d n z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberFiberAtGraphsSentence w R S r s a b c d n z x y)) := ZFReplay.replay (memberFiberAtGraphs_kernel_certificate w R S r s a b c d n z x y)

def memberFiberSentence {m} (w R S a b c d n z x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp (SyntaxRenameOutputSyntax.fiber w R S a b c d n)))).close

theorem source_memberFiber {m} (w R S a b c d n z x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberFiberSentence w R S a b c d n z x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomOutput.membership_fiber hZ w R S a b c d n z x y h0 h1 h2

theorem memberFiber_kernel_certificate {m} (w R S a b c d n z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberFiberSentence w R S a b c d n z x y)) := TheoryTransport.sentence (source_memberFiber w R S a b c d n z x y)

theorem native_memberFiber {m} (w R S a b c d n z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberFiberSentence w R S a b c d n z x y)) := ZFReplay.replay (memberFiber_kernel_certificate w R S a b c d n z x y)

def memberAllParametersSentence {m} (w n z x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp (SyntaxRenameOutputSyntax.property w n))).close

theorem source_memberAllParameters {m} (w n z x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberAllParametersSentence w n z x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomOutput.membership_property_all_parameters hZ w n z x y h0 h1

theorem memberAllParameters_kernel_certificate {m} (w n z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberAllParametersSentence w n z x y)) := TheoryTransport.sentence (source_memberAllParameters w n z x y)

theorem native_memberAllParameters {m} (w n z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberAllParametersSentence w n z x y)) := ZFReplay.replay (memberAllParameters_kernel_certificate w n z x y)

def memberBasePropertySentence {m} (w a b n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.membership w a b n).imp (SyntaxRenameOutputSyntax.property w n))).close

theorem source_memberBaseProperty {m} (w a b n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberBasePropertySentence w a b n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.membership w a b n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.membership w a b n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomicBase.membership_property hZ w a b n h0 h1

theorem memberBaseProperty_kernel_certificate {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberBasePropertySentence w a b n)) := TheoryTransport.sentence (source_memberBaseProperty w a b n)

theorem native_memberBaseProperty {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberBasePropertySentence w a b n)) := ZFReplay.replay (memberBaseProperty_kernel_certificate w a b n)

def atomicPropertySentence {m} (w a b n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.atomic w a b n).imp (SyntaxRenameOutputSyntax.property w n))).close

theorem source_atomicProperty {m} (w a b n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atomicPropertySentence w a b n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomicBase.property_of_atomic hZ w a b n h0 h1

theorem atomicProperty_kernel_certificate {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atomicPropertySentence w a b n)) := TheoryTransport.sentence (source_atomicProperty w a b n)

theorem native_atomicProperty {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atomicPropertySentence w a b n)) := ZFReplay.replay (atomicProperty_kernel_certificate w a b n)

def atomicFiberSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxAtomSyntax.atomic w a b n).imp (SyntaxRenameOutputSyntax.fiber w R S a b c d n)))).close

theorem source_atomicFiber {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atomicFiberSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomicBase.actual_fiber hZ w R S a b c d n h0 h1 h2

theorem atomicFiber_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atomicFiberSentence w R S a b c d n)) := TheoryTransport.sentence (source_atomicFiber w R S a b c d n)

theorem native_atomicFiber {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atomicFiberSentence w R S a b c d n)) := ZFReplay.replay (atomicFiber_kernel_certificate w R S a b c d n)

def atomicExistsSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxAtomSyntax.atomic w a b n).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n)))).close

theorem source_atomicExists {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atomicExistsSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomicBase.actual_exists hZ w R S a b c d n h0 h1 h2

theorem atomicExists_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atomicExistsSentence w R S a b c d n)) := TheoryTransport.sentence (source_atomicExists w R S a b c d n)

theorem native_atomicExists {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atomicExistsSentence w R S a b c d n)) := ZFReplay.replay (atomicExists_kernel_certificate w R S a b c d n)

end PPAC.Migration.Internal.ObjectSyntaxRenameAtomic
