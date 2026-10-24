import PPAC.Migration.Internal.ProjectAtomicData

/-! Actual original Project atomic compilation and exact internal subset expansion in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectProjectAtomic
open Source SourceAlgebra SourceLogic OmegaSyntax

def projectBoundShiftUniqueSentence {m} (w x y q : Fin m) : Source.Sentence := ((omega w).imp ((ProjectBoundShiftSyntax.shifted w x y).imp ((ProjectBoundShiftSyntax.shifted w x q).imp ((Formula.equal y q))))).close

theorem source_projectBoundShiftUnique {m} (w x y q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectBoundShiftUniqueSentence w x y q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectBoundShiftSyntax.shifted w x q) (Context.add (ProjectBoundShiftSyntax.shifted w x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectBoundShiftSyntax.shifted w x y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectBoundShiftSyntax.shifted w x q) := .hyp (Or.inl rfl)
  exact ProjectBoundShiftLaws.unique hZ w x y q h0 h1 h2

theorem projectBoundShiftUnique_kernel_certificate {m} (w x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectBoundShiftUniqueSentence w x y q)) := TheoryTransport.sentence (source_projectBoundShiftUnique w x y q)

theorem native_projectBoundShiftUnique {m} (w x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectBoundShiftUniqueSentence w x y q)) := ZFReplay.replay (projectBoundShiftUnique_kernel_certificate w x y q)

def projectBoundShiftRangeSentence {m} (w x y : Fin m) : Source.Sentence := ((omega w).imp ((ProjectBoundShiftSyntax.shifted w x y).imp ((Formula.mem y w)))).close

theorem source_projectBoundShiftRange {m} (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectBoundShiftRangeSentence w x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectBoundShiftSyntax.shifted w x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectBoundShiftSyntax.shifted w x y) := .hyp (Or.inl rfl)
  exact ProjectBoundShiftLaws.range hZ w x y h0 h1

theorem projectBoundShiftRange_kernel_certificate {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectBoundShiftRangeSentence w x y)) := TheoryTransport.sentence (source_projectBoundShiftRange w x y)

theorem native_projectBoundShiftRange {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectBoundShiftRangeSentence w x y)) := ZFReplay.replay (projectBoundShiftRange_kernel_certificate w x y)

def projectBoundShiftTargetTypeSentence {m} (w b B f x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((Formula.mem f w).imp ((successor B b).imp ((SyntaxTermSyntax.branch true w b x).imp ((ProjectBoundShiftSyntax.shifted w x y).imp ((SyntaxTermSyntax.term w B f y)))))))).close

theorem source_projectBoundShiftTargetType {m} (w b B f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectBoundShiftTargetTypeSentence w b B f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectBoundShiftSyntax.shifted w x y) (Context.add (SyntaxTermSyntax.branch true w b x) (Context.add (successor B b) (Context.add (Formula.mem f w) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem f w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor B b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTermSyntax.branch true w b x) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (ProjectBoundShiftSyntax.shifted w x y) := .hyp (Or.inl rfl)
  exact ProjectBoundShiftLaws.target_type hZ w b B f x y h0 h1 h2 h3 h4 h5

theorem projectBoundShiftTargetType_kernel_certificate {m} (w b B f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectBoundShiftTargetTypeSentence w b B f x y)) := TheoryTransport.sentence (source_projectBoundShiftTargetType w b B f x y)

theorem native_projectBoundShiftTargetType {m} (w b B f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectBoundShiftTargetTypeSentence w b B f x y)) := ZFReplay.replay (projectBoundShiftTargetType_kernel_certificate w b B f x y)

def projectBoundShiftExistsSentence {m} (w b x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.branch true w b x).imp ((ProjectBoundShiftSyntax.existsOutput w x)))).close

theorem source_projectBoundShiftExists {m} (w b x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectBoundShiftExistsSentence w b x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.branch true w b x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermSyntax.branch true w b x) := .hyp (Or.inl rfl)
  exact ProjectBoundShiftExistence.exists_output hZ w b x h0 h1

theorem projectBoundShiftExists_kernel_certificate {m} (w b x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectBoundShiftExistsSentence w b x)) := TheoryTransport.sentence (source_projectBoundShiftExists w b x)

theorem native_projectBoundShiftExists {m} (w b x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectBoundShiftExistsSentence w b x)) := ZFReplay.replay (projectBoundShiftExists_kernel_certificate w b x)

def projectBoundShiftExistsUniqueSentence {m} (w b x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.branch true w b x).imp ((ProjectBoundShiftSyntax.fiber w x)))).close

theorem source_projectBoundShiftExistsUnique {m} (w b x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectBoundShiftExistsUniqueSentence w b x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.branch true w b x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermSyntax.branch true w b x) := .hyp (Or.inl rfl)
  exact ProjectBoundShiftExistence.exists_unique hZ w b x h0 h1

theorem projectBoundShiftExistsUnique_kernel_certificate {m} (w b x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectBoundShiftExistsUniqueSentence w b x)) := TheoryTransport.sentence (source_projectBoundShiftExistsUnique w b x)

theorem native_projectBoundShiftExistsUnique {m} (w b x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectBoundShiftExistsUniqueSentence w b x)) := ZFReplay.replay (projectBoundShiftExistsUnique_kernel_certificate w b x)

def projectSubsetUniqueSentence {m} (w b z x y q r : Fin m) : Source.Sentence := ((omega w).imp ((ProjectSubsetSyntax.expanded w b z x y q).imp ((ProjectSubsetSyntax.expanded w b z x y r).imp ((Formula.equal q r))))).close

theorem source_projectSubsetUnique {m} (w b z x y q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSubsetUniqueSentence w b z x y q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSubsetSyntax.expanded w b z x y r) (Context.add (ProjectSubsetSyntax.expanded w b z x y q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectSubsetSyntax.expanded w b z x y q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectSubsetSyntax.expanded w b z x y r) := .hyp (Or.inl rfl)
  exact ProjectSubsetLaws.unique hZ w b z x y q r h0 h1 h2

theorem projectSubsetUnique_kernel_certificate {m} (w b z x y q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSubsetUniqueSentence w b z x y q r)) := TheoryTransport.sentence (source_projectSubsetUnique w b z x y q r)

theorem native_projectSubsetUnique {m} (w b z x y q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSubsetUniqueSentence w b z x y q r)) := ZFReplay.replay (projectSubsetUnique_kernel_certificate w b z x y q r)

def projectSubsetTargetTypeSentence {m} (w b z x y q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((empty z).imp ((SyntaxTermSyntax.branch true w b x).imp ((SyntaxTermSyntax.branch true w b y).imp ((ProjectSubsetSyntax.expanded w b z x y q).imp ((FormulaCodeSyntax.formulaCode w q b z)))))))).close

theorem source_projectSubsetTargetType {m} (w b z x y q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSubsetTargetTypeSentence w b z x y q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSubsetSyntax.expanded w b z x y q) (Context.add (SyntaxTermSyntax.branch true w b y) (Context.add (SyntaxTermSyntax.branch true w b x) (Context.add (empty z) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxTermSyntax.branch true w b x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTermSyntax.branch true w b y) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (ProjectSubsetSyntax.expanded w b z x y q) := .hyp (Or.inl rfl)
  exact ProjectSubsetLaws.target_type hZ w b z x y q h0 h1 h2 h3 h4 h5

theorem projectSubsetTargetType_kernel_certificate {m} (w b z x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSubsetTargetTypeSentence w b z x y q)) := TheoryTransport.sentence (source_projectSubsetTargetType w b z x y q)

theorem native_projectSubsetTargetType {m} (w b z x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSubsetTargetTypeSentence w b z x y q)) := ZFReplay.replay (projectSubsetTargetType_kernel_certificate w b z x y q)

def projectSubsetExistsSentence {m} (w b z x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((empty z).imp ((SyntaxTermSyntax.branch true w b x).imp ((SyntaxTermSyntax.branch true w b y).imp ((ProjectSubsetSyntax.existsOutput w b z x y))))))).close

theorem source_projectSubsetExists {m} (w b z x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSubsetExistsSentence w b z x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.branch true w b y) (Context.add (SyntaxTermSyntax.branch true w b x) (Context.add (empty z) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTermSyntax.branch true w b x) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTermSyntax.branch true w b y) := .hyp (Or.inl rfl)
  exact ProjectSubsetExistence.exists_output hZ w b z x y h0 h1 h2 h3 h4

theorem projectSubsetExists_kernel_certificate {m} (w b z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSubsetExistsSentence w b z x y)) := TheoryTransport.sentence (source_projectSubsetExists w b z x y)

theorem native_projectSubsetExists {m} (w b z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSubsetExistsSentence w b z x y)) := ZFReplay.replay (projectSubsetExists_kernel_certificate w b z x y)

def projectSubsetTypedUniqueSentence {m} (w b z x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((empty z).imp ((SyntaxTermSyntax.branch true w b x).imp ((SyntaxTermSyntax.branch true w b y).imp ((ProjectSubsetSyntax.fiber w b z x y))))))).close

theorem source_projectSubsetTypedUnique {m} (w b z x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSubsetTypedUniqueSentence w b z x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.branch true w b y) (Context.add (SyntaxTermSyntax.branch true w b x) (Context.add (empty z) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTermSyntax.branch true w b x) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTermSyntax.branch true w b y) := .hyp (Or.inl rfl)
  exact ProjectSubsetExistence.exists_unique_typed hZ w b z x y h0 h1 h2 h3 h4

theorem projectSubsetTypedUnique_kernel_certificate {m} (w b z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSubsetTypedUniqueSentence w b z x y)) := TheoryTransport.sentence (source_projectSubsetTypedUnique w b z x y)

theorem native_projectSubsetTypedUnique {m} (w b z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSubsetTypedUniqueSentence w b z x y)) := ZFReplay.replay (projectSubsetTypedUnique_kernel_certificate w b z x y)

def projectAtomicResultUniqueSentence {m} (kind : Fin 3) (w b z x y q r : Fin m) : Source.Sentence := ((omega w).imp ((ProjectAtomicSyntax.result kind w b z x y q).imp ((ProjectAtomicSyntax.result kind w b z x y r).imp ((Formula.equal q r))))).close

theorem source_projectAtomicResultUnique {m} (kind : Fin 3) (w b z x y q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectAtomicResultUniqueSentence kind w b z x y q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectAtomicSyntax.result kind w b z x y r) (Context.add (ProjectAtomicSyntax.result kind w b z x y q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectAtomicSyntax.result kind w b z x y q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectAtomicSyntax.result kind w b z x y r) := .hyp (Or.inl rfl)
  exact ProjectAtomicLaws.result_unique hZ kind w b z x y q r h0 h1 h2

theorem projectAtomicResultUnique_kernel_certificate {m} (kind : Fin 3) (w b z x y q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectAtomicResultUniqueSentence kind w b z x y q r)) := TheoryTransport.sentence (source_projectAtomicResultUnique kind w b z x y q r)

theorem native_projectAtomicResultUnique {m} (kind : Fin 3) (w b z x y q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectAtomicResultUniqueSentence kind w b z x y q r)) := ZFReplay.replay (projectAtomicResultUnique_kernel_certificate kind w b z x y q r)

def projectAtomicCompiledTypeSentence {m} (kind : Fin 3) (w b z x y n q : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectAtomicSyntax.compiled kind w b z x y n q).imp ((FormulaCodeSyntax.formulaCode w q b z))))).close

theorem source_projectAtomicCompiledType {m} (kind : Fin 3) (w b z x y n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectAtomicCompiledTypeSentence kind w b z x y n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectAtomicSyntax.compiled kind w b z x y n q) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectAtomicSyntax.compiled kind w b z x y n q) := .hyp (Or.inl rfl)
  exact ProjectAtomicLaws.compiled_type hZ kind w b z x y n q h0 h1 h2

theorem projectAtomicCompiledType_kernel_certificate {m} (kind : Fin 3) (w b z x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectAtomicCompiledTypeSentence kind w b z x y n q)) := TheoryTransport.sentence (source_projectAtomicCompiledType kind w b z x y n q)

theorem native_projectAtomicCompiledType {m} (kind : Fin 3) (w b z x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectAtomicCompiledTypeSentence kind w b z x y n q)) := ZFReplay.replay (projectAtomicCompiledType_kernel_certificate kind w b z x y n q)

def projectAtomicCompiledUniqueSentence {m} (kind : Fin 3) (w b z x y n q r : Fin m) : Source.Sentence := ((omega w).imp ((ProjectAtomicSyntax.compiled kind w b z x y n q).imp ((ProjectAtomicSyntax.compiled kind w b z x y n r).imp ((Formula.equal q r))))).close

theorem source_projectAtomicCompiledUnique {m} (kind : Fin 3) (w b z x y n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectAtomicCompiledUniqueSentence kind w b z x y n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectAtomicSyntax.compiled kind w b z x y n r) (Context.add (ProjectAtomicSyntax.compiled kind w b z x y n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectAtomicSyntax.compiled kind w b z x y n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectAtomicSyntax.compiled kind w b z x y n r) := .hyp (Or.inl rfl)
  exact ProjectAtomicLaws.compiled_unique hZ kind w b z x y n q r h0 h1 h2

theorem projectAtomicCompiledUnique_kernel_certificate {m} (kind : Fin 3) (w b z x y n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectAtomicCompiledUniqueSentence kind w b z x y n q r)) := TheoryTransport.sentence (source_projectAtomicCompiledUnique kind w b z x y n q r)

theorem native_projectAtomicCompiledUnique {m} (kind : Fin 3) (w b z x y n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectAtomicCompiledUniqueSentence kind w b z x y n q r)) := ZFReplay.replay (projectAtomicCompiledUnique_kernel_certificate kind w b z x y n q r)

def projectEqualitySameCodeSentence {m} (w b z x y n q : Fin m) : Source.Sentence := ((omega w).imp ((ProjectAtomicSyntax.compiled 1 w b z x y n q).imp ((Formula.equal q n)))).close

theorem source_projectEqualitySameCode {m} (w b z x y n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectEqualitySameCodeSentence w b z x y n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectAtomicSyntax.compiled 1 w b z x y n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectAtomicSyntax.compiled 1 w b z x y n q) := .hyp (Or.inl rfl)
  exact ProjectAtomicLaws.equal_same_code hZ w b z x y n q h0 h1

theorem projectEqualitySameCode_kernel_certificate {m} (w b z x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectEqualitySameCodeSentence w b z x y n q)) := TheoryTransport.sentence (source_projectEqualitySameCode w b z x y n q)

theorem native_projectEqualitySameCode {m} (w b z x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectEqualitySameCodeSentence w b z x y n q)) := ZFReplay.replay (projectEqualitySameCode_kernel_certificate w b z x y n q)

def projectAtomicTypedUniqueSentence {m} (kind : Fin 3) (w b z x y n : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectAtomicSyntax.sourceAt kind w b x y n).imp ((ProjectAtomicSyntax.fiber kind w b z x y n))))).close

theorem source_projectAtomicTypedUnique {m} (kind : Fin 3) (w b z x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectAtomicTypedUniqueSentence kind w b z x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectAtomicSyntax.sourceAt kind w b x y n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectAtomicSyntax.sourceAt kind w b x y n) := .hyp (Or.inl rfl)
  exact ProjectAtomicExistence.exists_unique_typed hZ kind w b z x y n h0 h1 h2

theorem projectAtomicTypedUnique_kernel_certificate {m} (kind : Fin 3) (w b z x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectAtomicTypedUniqueSentence kind w b z x y n)) := TheoryTransport.sentence (source_projectAtomicTypedUnique kind w b z x y n)

theorem native_projectAtomicTypedUnique {m} (kind : Fin 3) (w b z x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectAtomicTypedUniqueSentence kind w b z x y n)) := ZFReplay.replay (projectAtomicTypedUnique_kernel_certificate kind w b z x y n)

def projectAtomicAllInternalInputsSentence {m} (kind : Fin 3) (w z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectAtomicExistence.allInputs kind w z)))).close

theorem source_projectAtomicAllInternalInputs {m} (kind : Fin 3) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectAtomicAllInternalInputsSentence kind w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProjectAtomicExistence.all_internal_inputs hZ kind w z h0 h1

theorem projectAtomicAllInternalInputs_kernel_certificate {m} (kind : Fin 3) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectAtomicAllInternalInputsSentence kind w z)) := TheoryTransport.sentence (source_projectAtomicAllInternalInputs kind w z)

theorem native_projectAtomicAllInternalInputs {m} (kind : Fin 3) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectAtomicAllInternalInputsSentence kind w z)) := ZFReplay.replay (projectAtomicAllInternalInputs_kernel_certificate kind w z)

end PPAC.Migration.Internal.ObjectProjectAtomic
