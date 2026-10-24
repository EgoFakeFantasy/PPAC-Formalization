import PPAC.Migration.Internal.InstantiateFrameTypedAtomic
import PPAC.Migration.Internal.AtomicProgramMerge

/-! 任意内部深度mode2真实frame上，全部四原子输入的完整原Run3与既有独立原子程序等价。 -/
namespace PPAC.Migration.Internal.InstantiateFrameAtomic
open Source SourceAlgebra SourceLogic OmegaSyntax InstantiateOperationFrameSyntax

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hA : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaAtomicProgramSyntax.run w R S a b c e n q)) := by
  have hf : Derives Γ ((SyntaxAtomSyntax.nullary false w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.nullary false w a b c e n q))) := .impI (InstantiateFrameAtomicExisting.constant_iff (ZFContext.add hZ _) false w mode depth P a b c e R S n q (add hw _) (add hF _) (.hyp (Or.inl rfl)))
  have ht : Derives Γ ((SyntaxAtomSyntax.nullary true w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.nullary true w a b c e n q))) := .impI (InstantiateFrameAtomicExisting.constant_iff (ZFContext.add hZ _) true w mode depth P a b c e R S n q (add hw _) (add hF _) (.hyp (Or.inl rfl)))
  have hm : Derives Γ ((SyntaxAtomSyntax.membership w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.membership w R S a b c e n q))) := .impI (InstantiateFrameTypedAtomic.membership_iff (ZFContext.add hZ _) w mode depth P a b c e R S n q (add hw _) (add hF _) (.hyp (Or.inl rfl)))
  have he : Derives Γ ((SyntaxAtomSyntax.equality w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.equality w R S a b c e n q))) := .impI (InstantiateFrameTypedAtomic.equality_iff (ZFContext.add hZ _) w mode depth P a b c e R S n q (add hw _) (add hF _) (.hyp (Or.inl rfl)))
  exact AtomicProgramMerge.merge (OriginalTransformRowSyntax.run 3 w mode depth P n q) w R S a b c e n q hf ht hm he hA

theorem program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S h n q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hA : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R S a b c e h n q)) :=
  SyntaxRenameQuerySyntax.of_eq (congrArg (fun r => (OriginalTransformRowSyntax.run 3 w mode depth P n q).iff r) (FormulaAtomicProgramSyntax.run_eq_program w R S a b c e h n q))
    (run_iff hZ w mode depth P a b c e R S n q hw hF hA)

end PPAC.Migration.Internal.InstantiateFrameAtomic
