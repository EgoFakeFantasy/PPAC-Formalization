import PPAC.Migration.Internal.InstantiateFrameTerm
import PPAC.Migration.Internal.OriginalNumericTermValueTransfer

/-! 任意内部深度frame给出真实原Run1有类型唯一纤维及全部输入项的Promise证明。 -/
namespace PPAC.Migration.Internal.InstantiateFrameTermFiber
open Source SourceAlgebra SourceLogic OmegaSyntax InstantiateOperationFrameSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ (OriginalNumericTermValueSyntax.agreement w mode depth P R S n) := by
  apply Derives.allI
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hf1 := of_eq (frame_rename w mode depth P a b c e R S Fin.castSucc) (Derives.rename Fin.castSucc hF)
  have ht1 := of_eq (SyntaxTermSyntax.term_rename w a b n Fin.castSucc) (Derives.rename Fin.castSucc ht)
  exact InstantiateFrameTerm.program_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc e.castSucc R.castSucc S.castSucc n.castSucc (Fin.last m) hw1 hf1 ht1

theorem fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ (OriginalNumericTermValueSyntax.fiber w mode depth P c e n) := by
  have ha := agreement hZ w mode depth P a b c e R S n hw hF ht
  have hf := TermTransformProgramValue.actual_fiber hZ w R S a b c e n hw (.conjI (term_lists w mode depth P a b c e R S hF) ht)
  exact OriginalNumericTermValueTransfer.fiber_of_program w mode depth P R S a b c e n ha hf

theorem promise {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth P a b c e) := by
  apply Derives.allI
  apply Derives.impI
  let E := SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hf1 := of_eq (frame_rename w mode depth P a b c e R S Fin.castSucc) (under hF E)
  exact fiber (ZFContext.under hZ E) w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc e.castSucc R.castSucc S.castSucc (Fin.last m)
    hw1 hf1 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.InstantiateFrameTermFiber
