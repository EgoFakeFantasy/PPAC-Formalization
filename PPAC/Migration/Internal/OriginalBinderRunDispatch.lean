import PPAC.Migration.Internal.OriginalBinderCaseBridge

/-! 原两个量词处的完整十一分支排除与整条Run₃双条件。 -/
namespace PPAC.Migration.Internal.OriginalBinderRunDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalFormulaCaseSyntax
open OriginalFormulaTagRejection
open OriginalAtomicRunDispatch (disj_imp)

theorem outcomes_iff_quantified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w mode depth parameter n q x : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n)) :
    Derives Γ ((OriginalFormulaTraceEquation.outcomes w mode depth parameter n q).iff
      (binderCase (SyntaxLogicalSyntax.quantifierTag universal) w mode depth parameter n q)) := by
  cases universal with
  | false =>
    have h0 : Derives Γ ((OriginalFormulaLocalData.constant 0 w n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.botE (constant_rejected (ZFContext.add hZ _) 0 1 10 (by decide) w n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h1 : Derives Γ ((OriginalFormulaLocalData.constant 1 w n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.botE (constant_rejected (ZFContext.add hZ _) 1 1 10 (by decide) w n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h2 : Derives Γ ((applicationCase w mode depth parameter n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.botE (application_rejected (ZFContext.add hZ _) 1 10 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h3 : Derives Γ ((binaryCase 3 1 w mode depth parameter n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 3 1 1 10 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h4 : Derives Γ ((unaryCase 4 w mode depth parameter n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.botE (unary_rejected (ZFContext.add hZ _) 4 1 10 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h5 : Derives Γ ((binaryCase 5 3 w mode depth parameter n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 5 3 1 10 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h6 : Derives Γ ((binaryCase 6 3 w mode depth parameter n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 6 3 1 10 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h7 : Derives Γ ((binaryCase 7 3 w mode depth parameter n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 7 3 1 10 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h8 : Derives Γ ((binaryCase 8 3 w mode depth parameter n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 8 3 1 10 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h9 : Derives Γ ((binderCase 9 w mode depth parameter n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.botE (binder_rejected (ZFContext.add hZ _) 9 1 10 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h10 : Derives Γ ((binderCase 10 w mode depth parameter n q).imp (binderCase 10 w mode depth parameter n q)) := .impI (.hyp (Or.inl rfl))
    apply Derives.conjI
    · exact (disj_imp h0 (disj_imp h1 (disj_imp h2 (disj_imp h3 (disj_imp h4 (disj_imp h5 (disj_imp h6 (disj_imp h7 (disj_imp h8 (disj_imp h9 (disj_imp h10 (.impI (.botE (.hyp (Or.inl rfl)))))))))))))))
    · apply Derives.impI
      exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL (.hyp (Or.inl rfl))))))))))))
  | true =>
    have h0 : Derives Γ ((OriginalFormulaLocalData.constant 0 w n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.botE (constant_rejected (ZFContext.add hZ _) 0 1 9 (by decide) w n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h1 : Derives Γ ((OriginalFormulaLocalData.constant 1 w n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.botE (constant_rejected (ZFContext.add hZ _) 1 1 9 (by decide) w n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h2 : Derives Γ ((applicationCase w mode depth parameter n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.botE (application_rejected (ZFContext.add hZ _) 1 9 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h3 : Derives Γ ((binaryCase 3 1 w mode depth parameter n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 3 1 1 9 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h4 : Derives Γ ((unaryCase 4 w mode depth parameter n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.botE (unary_rejected (ZFContext.add hZ _) 4 1 9 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h5 : Derives Γ ((binaryCase 5 3 w mode depth parameter n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 5 3 1 9 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h6 : Derives Γ ((binaryCase 6 3 w mode depth parameter n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 6 3 1 9 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h7 : Derives Γ ((binaryCase 7 3 w mode depth parameter n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 7 3 1 9 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h8 : Derives Γ ((binaryCase 8 3 w mode depth parameter n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 8 3 1 9 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    have h9 : Derives Γ ((binderCase 9 w mode depth parameter n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.hyp (Or.inl rfl))
    have h10 : Derives Γ ((binderCase 10 w mode depth parameter n q).imp (binderCase 9 w mode depth parameter n q)) := .impI (.botE (binder_rejected (ZFContext.add hZ _) 10 1 9 (by decide) w mode depth parameter n q (fun _ => x) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
    apply Derives.conjI
    · exact (disj_imp h0 (disj_imp h1 (disj_imp h2 (disj_imp h3 (disj_imp h4 (disj_imp h5 (disj_imp h6 (disj_imp h7 (disj_imp h8 (disj_imp h9 (disj_imp h10 (.impI (.botE (.hyp (Or.inl rfl)))))))))))))))
    · apply Derives.impI
      exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL (.hyp (Or.inl rfl)))))))))))

theorem run_iff_quantified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three universal : Bool)
    (w mode depth parameter n q x : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff
      (binderCase (SyntaxLogicalSyntax.quantifierTag universal) w mode depth parameter n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaRunEquation.run_iff hZ three w mode depth parameter n q hw hm hd hp)
    (outcomes_iff_quantified hZ universal w mode depth parameter n q x hw hn)

end PPAC.Migration.Internal.OriginalBinderRunDispatch
