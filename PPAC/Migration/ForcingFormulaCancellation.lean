import PPAC.Migration.ForcingFormulaInduction
import PPAC.Migration.Internal.InstantiateTopFormulaOperation

/-! The ACTUAL same-root rebind / lifted opening / original mode2 formula
output equals direct opening. Completed original formula bridges are reused.
This is the body cancellation before actual guard/regularity and forcing MP. -/
namespace PPAC.Migration.ForcingFormulaCancellation
open Internal Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix
private def four {m} (a b c d : Fin m) : Fin 4 → Fin m := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

/-- Exact equality of actual full FORMULA codes. No child IH, externally
standard code bound, supplied equality or alternate operation is used. -/
theorem root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j n q I Y O P r s : Fin m) (d : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode)) (hz : Derives Γ (empty z))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hd : Derives Γ (ForcingConditionRebind.data w a f A j n q d)) (hj : Derives Γ (.mem j f))
    (hp : Derives Γ (StructuralListFieldSyntax.field w S j P))
    (hi : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s))
    (hopen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q I))
    (hrun : Derives Γ (OriginalTransformRowSyntax.run 3 w mode z P I Y))
    (hdirect : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a f z T n O)) : Derives Γ (.equal Y O) := by
  have hdiagram := ForcingTermDiagram.root hZ w mode z a f T A C R S K H j n q P r s d hw hm hz he hl hd hj hp hi
  have htype := SyntaxMixedFormulaJudgment.target_type w K H A f C T q I hopen
  have htop := Derives.impE (.conjL (InstantiateTopFormulaOperation.at_codes_iff hZ w mode z P T C r s I Y hw hm hz hi htype)) hrun
  have hcode := Derives.impE (.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ w z T C P I Y r s hw hi)) htop
  have hreb := Derives.conjR (.conjR (.conjR hd))
  exact ForcingFormulaInduction.cancel hZ w (four a A C z) (four f f T T) (four (d 3) K r R) (four (d 5) H s S)
    n q I Y O hw hdiagram hreb hopen hcode hdirect

def input {m} (w mode z a f T A C R S K H j n q I Y O P r s : Fin m) (d : Fin 6 → Fin m) : Formula m :=
  (ForcingTermDiagram.rootInput w mode z a f T A C R S K H j n q P r s d).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q I).conj
      ((OriginalTransformRowSyntax.run 3 w mode z P I Y).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a f z T n O)))

def sentence {m} (w mode z a f T A C R S K H j n q I Y O P r s : Fin m) (d : Fin 6 → Fin m) : Source.Sentence :=
  ((input w mode z a f T A C R S K H j n q I Y O P r s d).imp (.equal Y O)).close

theorem kernel_certificate {m} (w mode z a f T A C R S K H j n q I Y O P r s : Fin m) (d : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w mode z a f T A C R S K H j n q I Y O P r s d)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w mode z a f T A C R S K H j n q I Y O P r s d
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  have hb := Derives.conjL h
  have ho := Derives.conjL (.conjR h)
  have hr := Derives.conjL (.conjR (.conjR h))
  have hd := Derives.conjR (.conjR (.conjR h))
  exact root (ZFContext.add (ZFContext.source_ZF m) E) w mode z a f T A C R S K H j n q I Y O P r s d
    (.conjL hb) (.conjL (.conjR hb)) (.conjL (.conjR (.conjR hb)))
    (.conjL (.conjR (.conjR (.conjR hb)))) (.conjL (.conjR (.conjR (.conjR (.conjR hb)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hb)))))) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hb)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hb))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hb)))))))) ho hr hd

/-- Consume the ORIGINAL compiled rebind directly. Its SAME six compiler
witnesses are eliminated by original object existence rules. -/
theorem from_compiled {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j n q I Y O P r s : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hd : Derives Γ (ForcingConditionRebind.compiled w a f A j n q))
    (hj : Derives Γ (Formula.mem j f))
    (hp : Derives Γ (StructuralListFieldSyntax.field w S j P))
    (hi : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q I))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 3 w mode z P I Y))
    (hdir : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a f z T n O)) : Derives Γ (.equal Y O) := by
  let B := ForcingConditionRebind.data (HornBinderSyntax.old 6 w) (HornBinderSyntax.old 6 a) (HornBinderSyntax.old 6 f) (HornBinderSyntax.old 6 A)
    (HornBinderSyntax.old 6 j) (HornBinderSyntax.old 6 n) (HornBinderSyntax.old 6 q) (HornBinderSyntax.slot 6)
  let Δ := Context.add B (HornBinderSyntax.raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 B _ hd
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact root (HornBinderRules.zf_body 6 hZ B)
    (HornBinderSyntax.old 6 w) (HornBinderSyntax.old 6 mode) (HornBinderSyntax.old 6 z) (HornBinderSyntax.old 6 a) (HornBinderSyntax.old 6 f) (HornBinderSyntax.old 6 T) (HornBinderSyntax.old 6 A) (HornBinderSyntax.old 6 C) (HornBinderSyntax.old 6 R) (HornBinderSyntax.old 6 S) (HornBinderSyntax.old 6 K) (HornBinderSyntax.old 6 H) (HornBinderSyntax.old 6 j) (HornBinderSyntax.old 6 n) (HornBinderSyntax.old 6 q) (HornBinderSyntax.old 6 I) (HornBinderSyntax.old 6 Y) (HornBinderSyntax.old 6 O) (HornBinderSyntax.old 6 P) (HornBinderSyntax.old 6 r) (HornBinderSyntax.old 6 s) (HornBinderSyntax.slot 6)
    (of_eq (omega_rename w (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hw B))
    (of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hm B))
    (of_eq (empty_rename z (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hz B))
    (of_eq (ForcingOpenLayout.environment_rename w z a f T R S (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 he B))
    (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hl B))
    hB
    (HornBinderRules.under_body 6 hj B)
    (of_eq (StructuralListFieldSyntax.field_rename w S j P (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hp B))
    (of_eq (SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename w z T C P r s (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hi B))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T q I (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 ho B))
    (of_eq (OriginalTransformRowSyntax.run_rename 3 w mode z P I Y (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hr B))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R S a f z T n O (HornBinderSyntax.old 6)) (HornBinderRules.under_body 6 hdir B))

def compiledInput {m} (w mode z a f T A C R S K H j n q I Y O P r s : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj ((ForcingOpenLayout.environment w z a f T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj ((ForcingConditionRebind.compiled w a f A j n q).conj ((Formula.mem j f).conj ((StructuralListFieldSyntax.field w S j P).conj ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q I).conj ((OriginalTransformRowSyntax.run 3 w mode z P I Y).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a f z T n O))))))))))))

def compiledSentence {m} (w mode z a f T A C R S K H j n q I Y O P r s : Fin m) : Source.Sentence :=
  ((compiledInput w mode z a f T A C R S K H j n q I Y O P r s).imp (.equal Y O)).close

theorem compiled_kernel_certificate {m} (w mode z a f T A C R S K H j n q I Y O P r s : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (compiledSentence w mode z a f T A C R S K H j n q I Y O P r s)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := compiledInput w mode z a f T A C R S K H j n q I Y O P r s
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_compiled (ZFContext.add (ZFContext.source_ZF m) E) w mode z a f T A C R S K H j n q I Y O P r s
    (.conjL h)
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))))))

end PPAC.Migration.ForcingFormulaCancellation
