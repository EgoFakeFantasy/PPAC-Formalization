import PPAC.Migration.Internal.OriginalFormulaTraceEquation

/-! 十一数值分支的输入／输出自然性；无需预给根行或组件自然性。 -/
namespace PPAC.Migration.Internal.OriginalFormulaOutcomesNaturality
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax OriginalFormulaCaseSyntax OriginalFormulaTraceEquation
open SyntaxRenameQuerySyntax (of_eq)

theorem constant_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat)
    (w n q : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (OriginalFormulaLocalData.constant tag w n q)) :
    Derives Γ ((Formula.mem n w).conj (.mem q w)) :=
  .conjI (SyntaxNodeInjective.constructor_range hZ 0 tag w Fin.elim0 n hw (.conjL he))
    (SyntaxNodeInjective.constructor_range hZ 0 tag w Fin.elim0 q hw (.conjR he))

theorem binary_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag kind : Nat)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (binaryCase tag kind w mode depth parameter n q)) :
    Derives Γ ((Formula.mem n w).conj (.mem q w)) := by
  let B := binaryBody tag kind w mode depth parameter n q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ he
  have hZ1 := HornBinderRules.zf_body 4 hZ B
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .conjI (SyntaxNodeInjective.constructor_range hZ1 2 tag (old 4 w) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (old 4 n) hw1 (.conjL (.conjL hB)))
    (SyntaxNodeInjective.constructor_range hZ1 2 tag (old 4 w) (SyntaxAtomSyntax.two (slot 4 2) (slot 4 3)) (old 4 q) hw1 (.conjR (.conjL hB)))

theorem unary_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (unaryCase tag w mode depth parameter n q)) :
    Derives Γ ((Formula.mem n w).conj (.mem q w)) := by
  let B := unaryBody tag w mode depth parameter n q
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ he
  have hZ1 := HornBinderRules.zf_body 2 hZ B
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .conjI (SyntaxNodeInjective.constructor_range hZ1 1 tag (old 2 w) (fun _ => slot 2 0) (old 2 n) hw1 (.conjL (.conjL hB)))
    (SyntaxNodeInjective.constructor_range hZ1 1 tag (old 2 w) (fun _ => slot 2 1) (old 2 q) hw1 (.conjR (.conjL hB)))

theorem application_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (applicationCase w mode depth parameter n q)) :
    Derives Γ ((Formula.mem n w).conj (.mem q w)) := by
  let B := applicationBody w mode depth parameter n q
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ he
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .conjI (OriginalFormulaApplicationNaturality.output_natural hZ1 _ _ _ _ hw1 (.conjL (.conjL hB)))
    (OriginalFormulaApplicationNaturality.output_natural hZ1 _ _ _ _ hw1 (.conjR (.conjL hB)))

theorem binder_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (binderCase tag w mode depth parameter n q)) :
    Derives Γ ((Formula.mem n w).conj (.mem q w)) := by
  let B := binderBody tag w mode depth parameter n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  exact unary_natural (ZFContext.under hZ B) tag w.castSucc mode.castSucc (Fin.last m) parameter.castSucc n.castSucc q.castSucc hw1 (.conjR (.hyp (Or.inl rfl)))

theorem outcomes_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (outcomes w mode depth parameter n q)) :
    Derives Γ ((Formula.mem n w).conj (.mem q w)) := by
  apply Derives.disjE he
  · exact constant_natural (ZFContext.add hZ _) 0 w n q (add hw _) (.hyp (Or.inl rfl))
  · let Tail0 := (OriginalFormulaLocalData.constant 1 w n q).disj ((applicationCase w mode depth parameter n q).disj ((binaryCase 3 1 w mode depth parameter n q).disj ((unaryCase 4 w mode depth parameter n q).disj ((binaryCase 5 3 w mode depth parameter n q).disj ((binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot))))))))))
    have hZ0 := ZFContext.add hZ Tail0
    have hw0 := add hw Tail0
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact constant_natural (ZFContext.add hZ0 _) 1 w n q (add hw0 _) (.hyp (Or.inl rfl))
    · let Tail1 := (applicationCase w mode depth parameter n q).disj ((binaryCase 3 1 w mode depth parameter n q).disj ((unaryCase 4 w mode depth parameter n q).disj ((binaryCase 5 3 w mode depth parameter n q).disj ((binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot)))))))))
      have hZ1 := ZFContext.add hZ0 Tail1
      have hw1 := add hw0 Tail1
      apply Derives.disjE (.hyp (Or.inl rfl))
      · exact application_natural (ZFContext.add hZ1 _) w mode depth parameter n q (add hw1 _) (.hyp (Or.inl rfl))
      · let Tail2 := (binaryCase 3 1 w mode depth parameter n q).disj ((unaryCase 4 w mode depth parameter n q).disj ((binaryCase 5 3 w mode depth parameter n q).disj ((binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot))))))))
        have hZ2 := ZFContext.add hZ1 Tail2
        have hw2 := add hw1 Tail2
        apply Derives.disjE (.hyp (Or.inl rfl))
        · exact binary_natural (ZFContext.add hZ2 _) 3 1 w mode depth parameter n q (add hw2 _) (.hyp (Or.inl rfl))
        · let Tail3 := (unaryCase 4 w mode depth parameter n q).disj ((binaryCase 5 3 w mode depth parameter n q).disj ((binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot)))))))
          have hZ3 := ZFContext.add hZ2 Tail3
          have hw3 := add hw2 Tail3
          apply Derives.disjE (.hyp (Or.inl rfl))
          · exact unary_natural (ZFContext.add hZ3 _) 4 w mode depth parameter n q (add hw3 _) (.hyp (Or.inl rfl))
          · let Tail4 := (binaryCase 5 3 w mode depth parameter n q).disj ((binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot))))))
            have hZ4 := ZFContext.add hZ3 Tail4
            have hw4 := add hw3 Tail4
            apply Derives.disjE (.hyp (Or.inl rfl))
            · exact binary_natural (ZFContext.add hZ4 _) 5 3 w mode depth parameter n q (add hw4 _) (.hyp (Or.inl rfl))
            · let Tail5 := (binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot)))))
              have hZ5 := ZFContext.add hZ4 Tail5
              have hw5 := add hw4 Tail5
              apply Derives.disjE (.hyp (Or.inl rfl))
              · exact binary_natural (ZFContext.add hZ5 _) 6 3 w mode depth parameter n q (add hw5 _) (.hyp (Or.inl rfl))
              · let Tail6 := (binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot))))
                have hZ6 := ZFContext.add hZ5 Tail6
                have hw6 := add hw5 Tail6
                apply Derives.disjE (.hyp (Or.inl rfl))
                · exact binary_natural (ZFContext.add hZ6 _) 7 3 w mode depth parameter n q (add hw6 _) (.hyp (Or.inl rfl))
                · let Tail7 := (binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot)))
                  have hZ7 := ZFContext.add hZ6 Tail7
                  have hw7 := add hw6 Tail7
                  apply Derives.disjE (.hyp (Or.inl rfl))
                  · exact binary_natural (ZFContext.add hZ7 _) 8 3 w mode depth parameter n q (add hw7 _) (.hyp (Or.inl rfl))
                  · let Tail8 := (binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot))
                    have hZ8 := ZFContext.add hZ7 Tail8
                    have hw8 := add hw7 Tail8
                    apply Derives.disjE (.hyp (Or.inl rfl))
                    · exact binder_natural (ZFContext.add hZ8 _) 9 w mode depth parameter n q (add hw8 _) (.hyp (Or.inl rfl))
                    · let Tail9 := (binderCase 10 w mode depth parameter n q).disj (Formula.bot)
                      have hZ9 := ZFContext.add hZ8 Tail9
                      have hw9 := add hw8 Tail9
                      apply Derives.disjE (.hyp (Or.inl rfl))
                      · exact binder_natural (ZFContext.add hZ9 _) 10 w mode depth parameter n q (add hw9 _) (.hyp (Or.inl rfl))
                      · let Tail10 : Formula m := .bot
                        have hZ10 := ZFContext.add hZ9 Tail10
                        have hw10 := add hw9 Tail10
                        exact .botE (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalFormulaOutcomesNaturality
