import PPAC.Migration.Internal.AbstractUniformInductionSyntax
import PPAC.Migration.Internal.OriginalHistoryFromInduction

/-! 十参数统一IH在真实当前／binder提升frame上的内部实例，不要求绑定界相等或free表不变。 -/
namespace PPAC.Migration.Internal.AbstractUniformInductionRules
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax AbstractOperationFrameSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem prefix_at_frame {m} {Γ : Context m} (w n mode depth P a b c e R S : Fin m)
    (hi : Derives Γ (AbstractUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (OriginalFormulaInductionSyntax.prefixIH w mode depth P R S a b c e n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let G := (Formula.mem (slot 2 0) (old 2 n)).conj (FormulaCodeSyntax.formulaCode (old 2 w) (slot 2 0) (old 2 a) (old 2 b))
  let Δ := Context.add G (raisedContext 2 Γ)
  have hi1 : Derives Δ (AbstractUniformInductionSyntax.allFramesIH (old 2 w) (old 2 n)) := of_eq (AbstractUniformInductionSyntax.allFramesIH_rename w n (old 2)) (HornBinderRules.under_body 2 hi G)
  have hf1 : Derives Δ (frame (old 2 w) (old 2 mode) (old 2 depth) (old 2 P) (old 2 a) (old 2 b) (old 2 c) (old 2 e) (old 2 R) (old 2 S)) := of_eq (frame_rename w mode depth P a b c e R S (old 2)) (HornBinderRules.under_body 2 hf G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hc := AbstractUniformInductionSyntax.allFramesIH_at (old 2 w) (old 2 n) (slot 2 0) hi1 (.conjL hG)
  exact AbstractUniformInductionSyntax.correct_at (old 2 w) (slot 2 0) (old 2 mode) (old 2 depth) (old 2 P) (old 2 a) (old 2 b) (old 2 c) (old 2 e) (old 2 R) (old 2 S) (slot 2 1) hc hf1 (.conjR hG)

theorem agreement_at_frame {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n mode depth P a b c e R S h : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hi : Derives Γ (AbstractUniformInductionSyntax.allFramesIH w n)) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth P h R S a b c e n) :=
  OriginalHistoryFromInduction.from_graph hZ w mode depth P h R S a b c e n hw hn hg (prefix_at_frame w n mode depth P a b c e R S hi hf)

theorem agreed_history_at_frame {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n mode depth P a b c e R S : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hi : Derives Γ (AbstractUniformInductionSyntax.allFramesIH w n)) (hf : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (OriginalFormulaInductionSyntax.agreedHistory w mode depth P R S a b c e n) :=
  OriginalHistoryFromInduction.exists_agreed_history hZ w mode depth P R S a b c e n hw hn (prefix_at_frame w n mode depth P a b c e R S hi hf)

theorem binder_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n mode depth P a b c e R S A C K H D : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (AbstractUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (frame w mode depth P a b c e R S)) (hd : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H)) :
    Derives Γ (OriginalFormulaInductionSyntax.prefixIH w mode D P K H A b C e n) :=
  prefix_at_frame w n mode D P A b C e K H hi
    (AbstractOperationFrameBinder.lifted hZ w mode depth P D R S a b c e A C K H hw hf hd hl)

end PPAC.Migration.Internal.AbstractUniformInductionRules
