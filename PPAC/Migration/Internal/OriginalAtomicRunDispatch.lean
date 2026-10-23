import PPAC.Migration.Internal.OriginalFormulaTagRejection

/-! 原等词与两个常量处的完整Run₃分派；所有候选输出仍为内部集合变量。 -/
namespace PPAC.Migration.Internal.OriginalAtomicRunDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalFormulaCaseSyntax
open OriginalFormulaTagRejection

theorem disj_imp {m} {Γ : Context m} {p q r : Formula m}
    (hp : Derives Γ (p.imp r)) (hq : Derives Γ (q.imp r)) : Derives Γ ((p.disj q).imp r) := by
  apply Derives.impI
  apply Derives.disjE (.hyp (Or.inl rfl))
  · exact .impE (add (add hp _) _) (.hyp (Or.inl rfl))
  · exact .impE (add (add hq _) _) (.hyp (Or.inl rfl))

theorem outcomes_iff_false {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n)) :
    Derives Γ ((OriginalFormulaTraceEquation.outcomes w mode depth parameter n q).iff (OriginalFormulaLocalData.constant 0 w n q)) := by
  have h0 : Derives Γ ((OriginalFormulaLocalData.constant 0 w n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.hyp (Or.inl rfl))
  have h1 : Derives Γ ((OriginalFormulaLocalData.constant 1 w n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.botE (constant_rejected (ZFContext.add hZ _) 1 0 0 (by decide) w n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h2 : Derives Γ ((applicationCase w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.botE (application_rejected (ZFContext.add hZ _) 0 0 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h3 : Derives Γ ((binaryCase 3 1 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 3 1 0 0 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h4 : Derives Γ ((unaryCase 4 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.botE (unary_rejected (ZFContext.add hZ _) 4 0 0 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h5 : Derives Γ ((binaryCase 5 3 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 5 3 0 0 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h6 : Derives Γ ((binaryCase 6 3 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 6 3 0 0 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h7 : Derives Γ ((binaryCase 7 3 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 7 3 0 0 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h8 : Derives Γ ((binaryCase 8 3 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 8 3 0 0 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h9 : Derives Γ ((binderCase 9 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.botE (binder_rejected (ZFContext.add hZ _) 9 0 0 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h10 : Derives Γ ((binderCase 10 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 0 w n q)) := .impI (.botE (binder_rejected (ZFContext.add hZ _) 10 0 0 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  apply Derives.conjI
  · exact (disj_imp h0 (disj_imp h1 (disj_imp h2 (disj_imp h3 (disj_imp h4 (disj_imp h5 (disj_imp h6 (disj_imp h7 (disj_imp h8 (disj_imp h9 (disj_imp h10 (.impI (.botE (.hyp (Or.inl rfl)))))))))))))))
  · apply Derives.impI
    exact .disjL (.hyp (Or.inl rfl))

theorem run_iff_false {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaLocalData.constant 0 w n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaRunEquation.run_iff hZ three w mode depth parameter n q hw hm hd hp)
    (outcomes_iff_false hZ w mode depth parameter n q hw hn)

theorem outcomes_iff_true {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor 0 1 w Fin.elim0 n)) :
    Derives Γ ((OriginalFormulaTraceEquation.outcomes w mode depth parameter n q).iff (OriginalFormulaLocalData.constant 1 w n q)) := by
  have h0 : Derives Γ ((OriginalFormulaLocalData.constant 0 w n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.botE (constant_rejected (ZFContext.add hZ _) 0 0 1 (by decide) w n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h1 : Derives Γ ((OriginalFormulaLocalData.constant 1 w n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.hyp (Or.inl rfl))
  have h2 : Derives Γ ((applicationCase w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.botE (application_rejected (ZFContext.add hZ _) 0 1 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h3 : Derives Γ ((binaryCase 3 1 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 3 1 0 1 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h4 : Derives Γ ((unaryCase 4 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.botE (unary_rejected (ZFContext.add hZ _) 4 0 1 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h5 : Derives Γ ((binaryCase 5 3 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 5 3 0 1 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h6 : Derives Γ ((binaryCase 6 3 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 6 3 0 1 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h7 : Derives Γ ((binaryCase 7 3 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 7 3 0 1 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h8 : Derives Γ ((binaryCase 8 3 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 8 3 0 1 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h9 : Derives Γ ((binderCase 9 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.botE (binder_rejected (ZFContext.add hZ _) 9 0 1 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h10 : Derives Γ ((binderCase 10 w mode depth parameter n q).imp (OriginalFormulaLocalData.constant 1 w n q)) := .impI (.botE (binder_rejected (ZFContext.add hZ _) 10 0 1 (by decide) w mode depth parameter n q Fin.elim0 (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  apply Derives.conjI
  · exact (disj_imp h0 (disj_imp h1 (disj_imp h2 (disj_imp h3 (disj_imp h4 (disj_imp h5 (disj_imp h6 (disj_imp h7 (disj_imp h8 (disj_imp h9 (disj_imp h10 (.impI (.botE (.hyp (Or.inl rfl)))))))))))))))
  · apply Derives.impI
    exact .disjR (.disjL (.hyp (Or.inl rfl)))

theorem run_iff_true {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor 0 1 w Fin.elim0 n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaLocalData.constant 1 w n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaRunEquation.run_iff hZ three w mode depth parameter n q hw hm hd hp)
    (outcomes_iff_true hZ w mode depth parameter n q hw hn)

theorem outcomes_iff_equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter n q x y : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) :
    Derives Γ ((OriginalFormulaTraceEquation.outcomes w mode depth parameter n q).iff (binaryCase 3 1 w mode depth parameter n q)) := by
  have h0 : Derives Γ ((OriginalFormulaLocalData.constant 0 w n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.botE (constant_rejected (ZFContext.add hZ _) 0 2 3 (by decide) w n q (SyntaxAtomSyntax.two x y) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h1 : Derives Γ ((OriginalFormulaLocalData.constant 1 w n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.botE (constant_rejected (ZFContext.add hZ _) 1 2 3 (by decide) w n q (SyntaxAtomSyntax.two x y) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h2 : Derives Γ ((applicationCase w mode depth parameter n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.botE (application_rejected (ZFContext.add hZ _) 2 3 (by decide) w mode depth parameter n q (SyntaxAtomSyntax.two x y) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h3 : Derives Γ ((binaryCase 3 1 w mode depth parameter n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.hyp (Or.inl rfl))
  have h4 : Derives Γ ((unaryCase 4 w mode depth parameter n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.botE (unary_rejected (ZFContext.add hZ _) 4 2 3 (by decide) w mode depth parameter n q (SyntaxAtomSyntax.two x y) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h5 : Derives Γ ((binaryCase 5 3 w mode depth parameter n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 5 3 2 3 (by decide) w mode depth parameter n q (SyntaxAtomSyntax.two x y) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h6 : Derives Γ ((binaryCase 6 3 w mode depth parameter n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 6 3 2 3 (by decide) w mode depth parameter n q (SyntaxAtomSyntax.two x y) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h7 : Derives Γ ((binaryCase 7 3 w mode depth parameter n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 7 3 2 3 (by decide) w mode depth parameter n q (SyntaxAtomSyntax.two x y) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h8 : Derives Γ ((binaryCase 8 3 w mode depth parameter n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.botE (binary_rejected (ZFContext.add hZ _) 8 3 2 3 (by decide) w mode depth parameter n q (SyntaxAtomSyntax.two x y) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h9 : Derives Γ ((binderCase 9 w mode depth parameter n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.botE (binder_rejected (ZFContext.add hZ _) 9 2 3 (by decide) w mode depth parameter n q (SyntaxAtomSyntax.two x y) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  have h10 : Derives Γ ((binderCase 10 w mode depth parameter n q).imp (binaryCase 3 1 w mode depth parameter n q)) := .impI (.botE (binder_rejected (ZFContext.add hZ _) 10 2 3 (by decide) w mode depth parameter n q (SyntaxAtomSyntax.two x y) (add hw _) (add hn _) (.hyp (Or.inl rfl))))
  apply Derives.conjI
  · exact (disj_imp h0 (disj_imp h1 (disj_imp h2 (disj_imp h3 (disj_imp h4 (disj_imp h5 (disj_imp h6 (disj_imp h7 (disj_imp h8 (disj_imp h9 (disj_imp h10 (.impI (.botE (.hyp (Or.inl rfl)))))))))))))))
  · apply Derives.impI
    exact .disjR (.disjR (.disjR (.disjL (.hyp (Or.inl rfl)))))

theorem run_iff_equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter n q x y : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (binaryCase 3 1 w mode depth parameter n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaRunEquation.run_iff hZ three w mode depth parameter n q hw hm hd hp)
    (outcomes_iff_equality hZ w mode depth parameter n q x y hw hn)

end PPAC.Migration.Internal.OriginalAtomicRunDispatch
