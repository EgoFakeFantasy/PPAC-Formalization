import PPAC.Migration.Internal.FormulaCodeAllowedArity

/-! 全11实际带类型构造、接受根字段唯一解码/重编码及内部标签/字段数分类的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectFormulaCodeConstruction
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxForestSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxNumeralSyntax
open FormulaCodeSyntax FormulaCodeBranchSyntax FormulaCodeConstructSyntax FormulaCodeShapeSyntax FormulaCodeAllowedAritySyntax
open StructuralTreeOperatorSyntax (shape)
open StructuralTreeEncodeSyntax (encoding)

def fiberSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w b f : Fin m) : Source.Sentence := ((omega w).imp ((inputs k w xs).imp ((law k tag w xs b f).imp ((typedFiber k tag w xs b f))))).close

theorem source_fiber {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberSentence k tag xs w b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (law k tag w xs b f) (Context.add (inputs k w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (inputs k w xs) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (law k tag w xs b f) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.actual_fiber hZ k tag w xs b f h0 h1 h2

theorem fiber_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberSentence k tag xs w b f)) := TheoryTransport.sentence (source_fiber k tag xs w b f)

theorem native_fiber {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberSentence k tag xs w b f)) := ZFReplay.replay (fiber_kernel_certificate k tag xs w b f)

def existsOfFiberSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w b f : Fin m) : Source.Sentence := ((typedFiber k tag w xs b f).imp ((typedExists k tag w xs b f))).close

theorem source_existsOfFiber {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsOfFiberSentence k tag xs w b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (typedFiber k tag w xs b f) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (typedFiber k tag w xs b f) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber k tag w xs b f h0

theorem existsOfFiber_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsOfFiberSentence k tag xs w b f)) := TheoryTransport.sentence (source_existsOfFiber k tag xs w b f)

theorem native_existsOfFiber {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsOfFiberSentence k tag xs w b f)) := ZFReplay.replay (existsOfFiber_kernel_certificate k tag xs w b f)

def nullaryLawSentence {m} (truth : Bool) (w b f : Fin m) : Source.Sentence := ((omega w).imp ((contexts w b f).imp ((law 0 (nullaryTag truth) w (Fin.elim0) b f)))).close

theorem source_nullaryLaw {m} (truth : Bool) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryLawSentence truth w b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (contexts w b f) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.nullary_law hZ truth w b f h0 h1

theorem nullaryLaw_kernel_certificate {m} (truth : Bool) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryLawSentence truth w b f)) := TheoryTransport.sentence (source_nullaryLaw truth w b f)

theorem native_nullaryLaw {m} (truth : Bool) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryLawSentence truth w b f)) := ZFReplay.replay (nullaryLaw_kernel_certificate truth w b f)

def nullaryFiberSentence {m} (truth : Bool) (w b f : Fin m) : Source.Sentence := ((omega w).imp ((contexts w b f).imp ((typedFiber 0 (nullaryTag truth) w (Fin.elim0) b f)))).close

theorem source_nullaryFiber {m} (truth : Bool) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryFiberSentence truth w b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (contexts w b f) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.nullary hZ truth w b f h0 h1

theorem nullaryFiber_kernel_certificate {m} (truth : Bool) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryFiberSentence truth w b f)) := TheoryTransport.sentence (source_nullaryFiber truth w b f)

theorem native_nullaryFiber {m} (truth : Bool) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryFiberSentence truth w b f)) := ZFReplay.replay (nullaryFiber_kernel_certificate truth w b f)

def nullaryExistsSentence {m} (truth : Bool) (w b f : Fin m) : Source.Sentence := ((omega w).imp ((contexts w b f).imp ((typedExists 0 (nullaryTag truth) w (Fin.elim0) b f)))).close

theorem source_nullaryExists {m} (truth : Bool) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryExistsSentence truth w b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (contexts w b f) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber 0 (nullaryTag truth) w (Fin.elim0) b f (FormulaCodeConstructors.nullary hZ truth w b f h0 h1)

theorem nullaryExists_kernel_certificate {m} (truth : Bool) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryExistsSentence truth w b f)) := TheoryTransport.sentence (source_nullaryExists truth w b f)

theorem native_nullaryExists {m} (truth : Bool) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryExistsSentence truth w b f)) := ZFReplay.replay (nullaryExists_kernel_certificate truth w b f)

def memberLawSentence {m} (w b f s x y : Fin m) : Source.Sentence := ((omega w).imp ((memberTypes w b f s x y).imp ((law 3 (2) w (three s x y) b f)))).close

theorem source_memberLaw {m} (w b f s x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberLawSentence w b f s x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (memberTypes w b f s x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (memberTypes w b f s x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.member_law hZ w b f s x y h0 h1

theorem memberLaw_kernel_certificate {m} (w b f s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberLawSentence w b f s x y)) := TheoryTransport.sentence (source_memberLaw w b f s x y)

theorem native_memberLaw {m} (w b f s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberLawSentence w b f s x y)) := ZFReplay.replay (memberLaw_kernel_certificate w b f s x y)

def memberFiberSentence {m} (w b f s x y : Fin m) : Source.Sentence := ((omega w).imp ((memberTypes w b f s x y).imp ((typedFiber 3 (2) w (three s x y) b f)))).close

theorem source_memberFiber {m} (w b f s x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberFiberSentence w b f s x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (memberTypes w b f s x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (memberTypes w b f s x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.member hZ w b f s x y h0 h1

theorem memberFiber_kernel_certificate {m} (w b f s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberFiberSentence w b f s x y)) := TheoryTransport.sentence (source_memberFiber w b f s x y)

theorem native_memberFiber {m} (w b f s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberFiberSentence w b f s x y)) := ZFReplay.replay (memberFiber_kernel_certificate w b f s x y)

def memberExistsSentence {m} (w b f s x y : Fin m) : Source.Sentence := ((omega w).imp ((memberTypes w b f s x y).imp ((typedExists 3 (2) w (three s x y) b f)))).close

theorem source_memberExists {m} (w b f s x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberExistsSentence w b f s x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (memberTypes w b f s x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (memberTypes w b f s x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber 3 (2) w (three s x y) b f (FormulaCodeConstructors.member hZ w b f s x y h0 h1)

theorem memberExists_kernel_certificate {m} (w b f s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberExistsSentence w b f s x y)) := TheoryTransport.sentence (source_memberExists w b f s x y)

theorem native_memberExists {m} (w b f s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberExistsSentence w b f s x y)) := ZFReplay.replay (memberExists_kernel_certificate w b f s x y)

def equalLawSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((equalTypes w b f x y).imp ((law 2 (3) w (two x y) b f)))).close

theorem source_equalLaw {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalLawSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (equalTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (equalTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.equal_law hZ w b f x y h0 h1

theorem equalLaw_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalLawSentence w b f x y)) := TheoryTransport.sentence (source_equalLaw w b f x y)

theorem native_equalLaw {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalLawSentence w b f x y)) := ZFReplay.replay (equalLaw_kernel_certificate w b f x y)

def equalFiberSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((equalTypes w b f x y).imp ((typedFiber 2 (3) w (two x y) b f)))).close

theorem source_equalFiber {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalFiberSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (equalTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (equalTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.equal hZ w b f x y h0 h1

theorem equalFiber_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalFiberSentence w b f x y)) := TheoryTransport.sentence (source_equalFiber w b f x y)

theorem native_equalFiber {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalFiberSentence w b f x y)) := ZFReplay.replay (equalFiber_kernel_certificate w b f x y)

def equalExistsSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((equalTypes w b f x y).imp ((typedExists 2 (3) w (two x y) b f)))).close

theorem source_equalExists {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalExistsSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (equalTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (equalTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber 2 (3) w (two x y) b f (FormulaCodeConstructors.equal hZ w b f x y h0 h1)

theorem equalExists_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalExistsSentence w b f x y)) := TheoryTransport.sentence (source_equalExists w b f x y)

theorem native_equalExists {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalExistsSentence w b f x y)) := ZFReplay.replay (equalExists_kernel_certificate w b f x y)

def negationLawSentence {m} (w b f x : Fin m) : Source.Sentence := ((omega w).imp ((singleTypes false w b f x).imp ((law 1 (4) w (fun _ => x) b f)))).close

theorem source_negationLaw {m} (w b f x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationLawSentence w b f x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleTypes false w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleTypes false w b f x) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.negation_law hZ w b f x h0 h1

theorem negationLaw_kernel_certificate {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationLawSentence w b f x)) := TheoryTransport.sentence (source_negationLaw w b f x)

theorem native_negationLaw {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationLawSentence w b f x)) := ZFReplay.replay (negationLaw_kernel_certificate w b f x)

def negationFiberSentence {m} (w b f x : Fin m) : Source.Sentence := ((omega w).imp ((singleTypes false w b f x).imp ((typedFiber 1 (4) w (fun _ => x) b f)))).close

theorem source_negationFiber {m} (w b f x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationFiberSentence w b f x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleTypes false w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleTypes false w b f x) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.negation hZ w b f x h0 h1

theorem negationFiber_kernel_certificate {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationFiberSentence w b f x)) := TheoryTransport.sentence (source_negationFiber w b f x)

theorem native_negationFiber {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationFiberSentence w b f x)) := ZFReplay.replay (negationFiber_kernel_certificate w b f x)

def negationExistsSentence {m} (w b f x : Fin m) : Source.Sentence := ((omega w).imp ((singleTypes false w b f x).imp ((typedExists 1 (4) w (fun _ => x) b f)))).close

theorem source_negationExists {m} (w b f x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationExistsSentence w b f x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleTypes false w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleTypes false w b f x) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber 1 (4) w (fun _ => x) b f (FormulaCodeConstructors.negation hZ w b f x h0 h1)

theorem negationExists_kernel_certificate {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationExistsSentence w b f x)) := TheoryTransport.sentence (source_negationExists w b f x)

theorem native_negationExists {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationExistsSentence w b f x)) := ZFReplay.replay (negationExists_kernel_certificate w b f x)

def forallLawSentence {m} (w b f x : Fin m) : Source.Sentence := ((omega w).imp ((singleTypes true w b f x).imp ((law 1 (9) w (fun _ => x) b f)))).close

theorem source_forallLaw {m} (w b f x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallLawSentence w b f x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleTypes true w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleTypes true w b f x) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.forall_law hZ w b f x h0 h1

theorem forallLaw_kernel_certificate {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallLawSentence w b f x)) := TheoryTransport.sentence (source_forallLaw w b f x)

theorem native_forallLaw {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallLawSentence w b f x)) := ZFReplay.replay (forallLaw_kernel_certificate w b f x)

def forallFiberSentence {m} (w b f x : Fin m) : Source.Sentence := ((omega w).imp ((singleTypes true w b f x).imp ((typedFiber 1 (9) w (fun _ => x) b f)))).close

theorem source_forallFiber {m} (w b f x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallFiberSentence w b f x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleTypes true w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleTypes true w b f x) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.universal hZ w b f x h0 h1

theorem forallFiber_kernel_certificate {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallFiberSentence w b f x)) := TheoryTransport.sentence (source_forallFiber w b f x)

theorem native_forallFiber {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallFiberSentence w b f x)) := ZFReplay.replay (forallFiber_kernel_certificate w b f x)

def forallExistsSentence {m} (w b f x : Fin m) : Source.Sentence := ((omega w).imp ((singleTypes true w b f x).imp ((typedExists 1 (9) w (fun _ => x) b f)))).close

theorem source_forallExists {m} (w b f x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallExistsSentence w b f x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleTypes true w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleTypes true w b f x) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber 1 (9) w (fun _ => x) b f (FormulaCodeConstructors.universal hZ w b f x h0 h1)

theorem forallExists_kernel_certificate {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallExistsSentence w b f x)) := TheoryTransport.sentence (source_forallExists w b f x)

theorem native_forallExists {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallExistsSentence w b f x)) := ZFReplay.replay (forallExists_kernel_certificate w b f x)

def existsLawSentence {m} (w b f x : Fin m) : Source.Sentence := ((omega w).imp ((singleTypes true w b f x).imp ((law 1 (10) w (fun _ => x) b f)))).close

theorem source_existsLaw {m} (w b f x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsLawSentence w b f x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleTypes true w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleTypes true w b f x) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.exists_law hZ w b f x h0 h1

theorem existsLaw_kernel_certificate {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsLawSentence w b f x)) := TheoryTransport.sentence (source_existsLaw w b f x)

theorem native_existsLaw {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsLawSentence w b f x)) := ZFReplay.replay (existsLaw_kernel_certificate w b f x)

def existsFiberSentence {m} (w b f x : Fin m) : Source.Sentence := ((omega w).imp ((singleTypes true w b f x).imp ((typedFiber 1 (10) w (fun _ => x) b f)))).close

theorem source_existsFiber {m} (w b f x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsFiberSentence w b f x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleTypes true w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleTypes true w b f x) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.existential hZ w b f x h0 h1

theorem existsFiber_kernel_certificate {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsFiberSentence w b f x)) := TheoryTransport.sentence (source_existsFiber w b f x)

theorem native_existsFiber {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsFiberSentence w b f x)) := ZFReplay.replay (existsFiber_kernel_certificate w b f x)

def existsExistsSentence {m} (w b f x : Fin m) : Source.Sentence := ((omega w).imp ((singleTypes true w b f x).imp ((typedExists 1 (10) w (fun _ => x) b f)))).close

theorem source_existsExists {m} (w b f x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsExistsSentence w b f x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleTypes true w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleTypes true w b f x) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber 1 (10) w (fun _ => x) b f (FormulaCodeConstructors.existential hZ w b f x h0 h1)

theorem existsExists_kernel_certificate {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsExistsSentence w b f x)) := TheoryTransport.sentence (source_existsExists w b f x)

theorem native_existsExists {m} (w b f x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsExistsSentence w b f x)) := ZFReplay.replay (existsExists_kernel_certificate w b f x)

def binary0LawSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((law 2 (5) w (two x y) b f)))).close

theorem source_binary0Law {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary0LawSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.binary0_law hZ w b f x y h0 h1

theorem binary0Law_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary0LawSentence w b f x y)) := TheoryTransport.sentence (source_binary0Law w b f x y)

theorem native_binary0Law {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary0LawSentence w b f x y)) := ZFReplay.replay (binary0Law_kernel_certificate w b f x y)

def binary0FiberSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((typedFiber 2 (5) w (two x y) b f)))).close

theorem source_binary0Fiber {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary0FiberSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.binary0 hZ w b f x y h0 h1

theorem binary0Fiber_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary0FiberSentence w b f x y)) := TheoryTransport.sentence (source_binary0Fiber w b f x y)

theorem native_binary0Fiber {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary0FiberSentence w b f x y)) := ZFReplay.replay (binary0Fiber_kernel_certificate w b f x y)

def binary0ExistsSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((typedExists 2 (5) w (two x y) b f)))).close

theorem source_binary0Exists {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary0ExistsSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber 2 (5) w (two x y) b f (FormulaCodeConstructors.binary0 hZ w b f x y h0 h1)

theorem binary0Exists_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary0ExistsSentence w b f x y)) := TheoryTransport.sentence (source_binary0Exists w b f x y)

theorem native_binary0Exists {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary0ExistsSentence w b f x y)) := ZFReplay.replay (binary0Exists_kernel_certificate w b f x y)

def binary1LawSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((law 2 (6) w (two x y) b f)))).close

theorem source_binary1Law {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary1LawSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.binary1_law hZ w b f x y h0 h1

theorem binary1Law_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary1LawSentence w b f x y)) := TheoryTransport.sentence (source_binary1Law w b f x y)

theorem native_binary1Law {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary1LawSentence w b f x y)) := ZFReplay.replay (binary1Law_kernel_certificate w b f x y)

def binary1FiberSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((typedFiber 2 (6) w (two x y) b f)))).close

theorem source_binary1Fiber {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary1FiberSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.binary1 hZ w b f x y h0 h1

theorem binary1Fiber_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary1FiberSentence w b f x y)) := TheoryTransport.sentence (source_binary1Fiber w b f x y)

theorem native_binary1Fiber {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary1FiberSentence w b f x y)) := ZFReplay.replay (binary1Fiber_kernel_certificate w b f x y)

def binary1ExistsSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((typedExists 2 (6) w (two x y) b f)))).close

theorem source_binary1Exists {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary1ExistsSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber 2 (6) w (two x y) b f (FormulaCodeConstructors.binary1 hZ w b f x y h0 h1)

theorem binary1Exists_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary1ExistsSentence w b f x y)) := TheoryTransport.sentence (source_binary1Exists w b f x y)

theorem native_binary1Exists {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary1ExistsSentence w b f x y)) := ZFReplay.replay (binary1Exists_kernel_certificate w b f x y)

def binary2LawSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((law 2 (7) w (two x y) b f)))).close

theorem source_binary2Law {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary2LawSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.binary2_law hZ w b f x y h0 h1

theorem binary2Law_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary2LawSentence w b f x y)) := TheoryTransport.sentence (source_binary2Law w b f x y)

theorem native_binary2Law {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary2LawSentence w b f x y)) := ZFReplay.replay (binary2Law_kernel_certificate w b f x y)

def binary2FiberSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((typedFiber 2 (7) w (two x y) b f)))).close

theorem source_binary2Fiber {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary2FiberSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.binary2 hZ w b f x y h0 h1

theorem binary2Fiber_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary2FiberSentence w b f x y)) := TheoryTransport.sentence (source_binary2Fiber w b f x y)

theorem native_binary2Fiber {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary2FiberSentence w b f x y)) := ZFReplay.replay (binary2Fiber_kernel_certificate w b f x y)

def binary2ExistsSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((typedExists 2 (7) w (two x y) b f)))).close

theorem source_binary2Exists {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary2ExistsSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber 2 (7) w (two x y) b f (FormulaCodeConstructors.binary2 hZ w b f x y h0 h1)

theorem binary2Exists_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary2ExistsSentence w b f x y)) := TheoryTransport.sentence (source_binary2Exists w b f x y)

theorem native_binary2Exists {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary2ExistsSentence w b f x y)) := ZFReplay.replay (binary2Exists_kernel_certificate w b f x y)

def binary3LawSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((law 2 (8) w (two x y) b f)))).close

theorem source_binary3Law {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary3LawSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.binary3_law hZ w b f x y h0 h1

theorem binary3Law_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary3LawSentence w b f x y)) := TheoryTransport.sentence (source_binary3Law w b f x y)

theorem native_binary3Law {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary3LawSentence w b f x y)) := ZFReplay.replay (binary3Law_kernel_certificate w b f x y)

def binary3FiberSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((typedFiber 2 (8) w (two x y) b f)))).close

theorem source_binary3Fiber {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary3FiberSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.binary3 hZ w b f x y h0 h1

theorem binary3Fiber_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary3FiberSentence w b f x y)) := TheoryTransport.sentence (source_binary3Fiber w b f x y)

theorem native_binary3Fiber {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary3FiberSentence w b f x y)) := ZFReplay.replay (binary3Fiber_kernel_certificate w b f x y)

def binary3ExistsSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryTypes w b f x y).imp ((typedExists 2 (8) w (two x y) b f)))).close

theorem source_binary3Exists {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary3ExistsSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryTypes w b f x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryTypes w b f x y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstruct.exists_of_fiber 2 (8) w (two x y) b f (FormulaCodeConstructors.binary3 hZ w b f x y h0 h1)

theorem binary3Exists_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary3ExistsSentence w b f x y)) := TheoryTransport.sentence (source_binary3Exists w b f x y)

theorem native_binary3Exists {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary3ExistsSentence w b f x y)) := ZFReplay.replay (binary3Exists_kernel_certificate w b f x y)

def membershipFiberSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((term w b f x).imp ((term w b f y).imp ((FormulaCodeConstructors.membershipFiber w b f x y))))).close

theorem source_membershipFiber {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipFiberSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (term w b f y) (Context.add (term w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (term w b f x) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (term w b f y) := .hyp (Or.inl rfl)
  exact FormulaCodeConstructors.membership hZ w b f x y h0 h1 h2

theorem membershipFiber_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipFiberSentence w b f x y)) := TheoryTransport.sentence (source_membershipFiber w b f x y)

theorem native_membershipFiber {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipFiberSentence w b f x y)) := ZFReplay.replay (membershipFiber_kernel_certificate w b f x y)

def forestValidSentence {m} (k : Nat) (xs : Fin k → Fin m) (w p : Fin m) : Source.Sentence := ((omega w).imp ((forest k w xs p).imp ((StructuralListTraceSyntax.valid w p)))).close

theorem source_forestValid {m} (k : Nat) (xs : Fin k → Fin m) (w p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestValidSentence k xs w p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (forest k w xs p) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (forest k w xs p) := .hyp (Or.inl rfl)
  exact FormulaCodeShape.forest_valid hZ k w xs p h0 h1

theorem forestValid_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestValidSentence k xs w p)) := TheoryTransport.sentence (source_forestValid k xs w p)

theorem native_forestValid {m} (k : Nat) (xs : Fin k → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestValidSentence k xs w p)) := ZFReplay.replay (forestValid_kernel_certificate k xs w p)

def nodeShapeSentence {m} (k : Nat) (xs : Fin k → Fin m) (w t n : Fin m) : Source.Sentence := ((omega w).imp ((node k w t xs n).imp ((shapeFiber w n)))).close

theorem source_nodeShape {m} (k : Nat) (xs : Fin k → Fin m) (w t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nodeShapeSentence k xs w t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (node k w t xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (node k w t xs n) := .hyp (Or.inl rfl)
  exact FormulaCodeShape.from_node hZ k w t xs n h0 h1

theorem nodeShape_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nodeShapeSentence k xs w t n)) := TheoryTransport.sentence (source_nodeShape k xs w t n)

theorem native_nodeShape {m} (k : Nat) (xs : Fin k → Fin m) (w t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nodeShapeSentence k xs w t n)) := ZFReplay.replay (nodeShape_kernel_certificate k xs w t n)

def constructorShapeSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shapeFiber w n)))).close

theorem source_constructorShape {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constructorShapeSentence k tag xs w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inl rfl)
  exact FormulaCodeShape.from_constructor hZ k tag w xs n h0 h1

theorem constructorShape_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorShapeSentence k tag xs w n)) := TheoryTransport.sentence (source_constructorShape k tag xs w n)

theorem native_constructorShape {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorShapeSentence k tag xs w n)) := ZFReplay.replay (constructorShape_kernel_certificate k tag xs w n)

def shapeUniqueSentence {m} (w n t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp ((uniqueShape w n t p l g)))).close

theorem source_shapeUnique {m} (w n t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (shapeUniqueSentence w n t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeShape.unique_formula hZ w n t p l g h0 h1

theorem shapeUnique_kernel_certificate {m} (w n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (shapeUniqueSentence w n t p l g)) := TheoryTransport.sentence (source_shapeUnique w n t p l g)

theorem native_shapeUnique {m} (w n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (shapeUniqueSentence w n t p l g)) := ZFReplay.replay (shapeUnique_kernel_certificate w n t p l g)

def acceptedShapeSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((formulaCode w n b f).imp ((shapeFiber w n)))).close

theorem source_acceptedShape {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (acceptedShapeSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeAcceptedShape.accepted hZ w n b f h0 h1

theorem acceptedShape_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (acceptedShapeSentence w n b f)) := TheoryTransport.sentence (source_acceptedShape w n b f)

theorem native_acceptedShape {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (acceptedShapeSentence w n b f)) := ZFReplay.replay (acceptedShape_kernel_certificate w n b f)

def reencodingSentence {m} (w n b f t p l g r : Fin m) : Source.Sentence := ((omega w).imp ((formulaCode w n b f).imp ((shape w n t p l g).imp ((encoding w t l g r).imp (((Formula.equal r n).conj (formulaCode w r b f))))))).close

theorem source_reencoding {m} (w n b f t p l g r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (reencodingSentence w n b f t p l g r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (encoding w t l g r) (Context.add (shape w n t p l g) (Context.add (formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (encoding w t l g r) := .hyp (Or.inl rfl)
  exact FormulaCodeAcceptedShape.reencoding hZ w n b f t p l g r h0 h1 h2 h3

theorem reencoding_kernel_certificate {m} (w n b f t p l g r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (reencodingSentence w n b f t p l g r)) := TheoryTransport.sentence (source_reencoding w n b f t p l g r)

theorem native_reencoding {m} (w n b f t p l g r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (reencodingSentence w n b f t p l g r)) := ZFReplay.replay (reencoding_kernel_certificate w n b f t p l g r)

def roundTripSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((formulaCode w n b f).imp ((shape w n t p l g).imp ((FormulaCodeAcceptedShape.roundTripAt w n b f t p l g))))).close

theorem source_roundTrip {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (roundTripSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeAcceptedShape.at_shape hZ w n b f t p l g h0 h1 h2

theorem roundTrip_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (roundTripSentence w n b f t p l g)) := TheoryTransport.sentence (source_roundTrip w n b f t p l g)

theorem native_roundTrip {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (roundTripSentence w n b f t p l g)) := ZFReplay.replay (roundTrip_kernel_certificate w n b f t p l g)

def forestAritySentence {m} (k : Nat) (xs : Fin k → Fin m) (w p l : Fin m) : Source.Sentence := ((omega w).imp ((forest k w xs p).imp ((StructuralListLengthSyntax.hasLength w p l).imp ((numeral k l))))).close

theorem source_forestArity {m} (k : Nat) (xs : Fin k → Fin m) (w p l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestAritySentence k xs w p l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListLengthSyntax.hasLength w p l) (Context.add (forest k w xs p) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (forest k w xs p) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListLengthSyntax.hasLength w p l) := .hyp (Or.inl rfl)
  exact FormulaCodeFieldArity.forest_length hZ k w xs p l h0 h1 h2

theorem forestArity_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w p l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestAritySentence k xs w p l)) := TheoryTransport.sentence (source_forestArity k xs w p l)

theorem native_forestArity {m} (k : Nat) (xs : Fin k → Fin m) (w p l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestAritySentence k xs w p l)) := ZFReplay.replay (forestArity_kernel_certificate k xs w p l)

def nodeAritySentence {m} (k : Nat) (xs : Fin k → Fin m) (w t n a p l g : Fin m) : Source.Sentence := ((omega w).imp ((node k w t xs n).imp ((shape w n a p l g).imp ((numeral k l))))).close

theorem source_nodeArity {m} (k : Nat) (xs : Fin k → Fin m) (w t n a p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nodeAritySentence k xs w t n a p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n a p l g) (Context.add (node k w t xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (node k w t xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n a p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeFieldArity.node_length hZ k w t xs n a p l g h0 h1 h2

theorem nodeArity_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w t n a p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nodeAritySentence k xs w t n a p l g)) := TheoryTransport.sentence (source_nodeArity k xs w t n a p l g)

theorem native_nodeArity {m} (k : Nat) (xs : Fin k → Fin m) (w t n a p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nodeAritySentence k xs w t n a p l g)) := ZFReplay.replay (nodeArity_kernel_certificate k xs w t n a p l g)

def constructorAritySentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n a p l g : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shape w n a p l g).imp ((numeral k l))))).close

theorem source_constructorArity {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n a p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constructorAritySentence k tag xs w n a p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n a p l g) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n a p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeFieldArity.constructor_length hZ k tag w xs n a p l g h0 h1 h2

theorem constructorArity_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n a p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorAritySentence k tag xs w n a p l g)) := TheoryTransport.sentence (source_constructorArity k tag xs w n a p l g)

theorem native_constructorArity {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n a p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorAritySentence k tag xs w n a p l g)) := ZFReplay.replay (constructorArity_kernel_certificate k tag xs w n a p l g)

def constructorTagSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n a p l g : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shape w n a p l g).imp ((numeral tag a))))).close

theorem source_constructorTag {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n a p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constructorTagSentence k tag xs w n a p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n a p l g) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n a p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeFieldArity.constructor_tag hZ k tag w xs n a p l g h0 h1 h2

theorem constructorTag_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n a p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorTagSentence k tag xs w n a p l g)) := TheoryTransport.sentence (source_constructorTag k tag xs w n a p l g)

theorem native_constructorTag {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n a p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorTagSentence k tag xs w n a p l g)) := ZFReplay.replay (constructorTag_kernel_certificate k tag xs w n a p l g)

def allowedAritySentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((formulaCode w n b f).imp ((shape w n t p l g).imp ((allowed 11 t l))))).close

theorem source_allowedArity {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allowedAritySentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeAllowedArity.accepted hZ w n b f t p l g h0 h1 h2

theorem allowedArity_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allowedAritySentence w n b f t p l g)) := TheoryTransport.sentence (source_allowedArity w n b f t p l g)

theorem native_allowedArity {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allowedAritySentence w n b f t p l g)) := ZFReplay.replay (allowedArity_kernel_certificate w n b f t p l g)

def rejectAritySentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp (((allowed 11 t l).neg).imp (((formulaCode w n b f).neg))))).close

theorem source_rejectArity {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectAritySentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((allowed 11 t l).neg) (Context.add (shape w n t p l g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((allowed 11 t l).neg) := .hyp (Or.inl rfl)
  exact FormulaCodeAllowedArity.reject hZ w n b f t p l g h0 h1 h2

theorem rejectArity_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectAritySentence w n b f t p l g)) := TheoryTransport.sentence (source_rejectArity w n b f t p l g)

theorem native_rejectArity {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectAritySentence w n b f t p l g)) := ZFReplay.replay (rejectArity_kernel_certificate w n b f t p l g)

end PPAC.Migration.Internal.ObjectFormulaCodeConstruction
