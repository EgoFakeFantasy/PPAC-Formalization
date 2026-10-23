import PPAC.Migration.Internal.MemberProgramCase

/-! 已知纯成员输入处排除其余十个公式分支，得到原完整Run₃的精确成员分派。 -/
namespace PPAC.Migration.Internal.OriginalMemberRunDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax OriginalFormulaCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem constant_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (hne : tag ≠ 2)
    (w s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (he : Derives Γ (OriginalFormulaLocalData.constant tag w n q)) : Derives Γ .bot :=
  SyntaxConstructors.disjoint hZ 0 3 tag 2 hne w Fin.elim0 (SyntaxAtomSyntax.three s x y) n hw (.conjL he) hn

theorem binary_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag kind : Nat) (hne : tag ≠ 2)
    (w mode depth parameter s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (he : Derives Γ (binaryCase tag kind w mode depth parameter n q)) : Derives Γ .bot := by
  let B := binaryBody tag kind w mode depth parameter n q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ he
  have hZ1 := HornBinderRules.zf_body 4 hZ B
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hn1 : Derives Δ (SyntaxAtomSyntax.memberCode (old 4 w) (old 4 s) (old 4 x) (old 4 y) (old 4 n)) := of_eq (SyntaxAtomSyntax.memberCode_rename w s x y n (old 4)) (HornBinderRules.under_body 4 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint hZ1 2 3 tag 2 hne (old 4 w) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (SyntaxAtomSyntax.three (old 4 s) (old 4 x) (old 4 y)) (old 4 n) hw1 (.conjL (.conjL hB)) hn1

theorem unary_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (hne : tag ≠ 2)
    (w mode depth parameter s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (he : Derives Γ (unaryCase tag w mode depth parameter n q)) : Derives Γ .bot := by
  let B := unaryBody tag w mode depth parameter n q
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ he
  have hZ1 := HornBinderRules.zf_body 2 hZ B
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hn1 : Derives Δ (SyntaxAtomSyntax.memberCode (old 2 w) (old 2 s) (old 2 x) (old 2 y) (old 2 n)) := of_eq (SyntaxAtomSyntax.memberCode_rename w s x y n (old 2)) (HornBinderRules.under_body 2 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint hZ1 1 3 tag 2 hne (old 2 w) (fun _ => slot 2 0) (SyntaxAtomSyntax.three (old 2 s) (old 2 x) (old 2 y)) (old 2 n) hw1 (.conjL (.conjL hB)) hn1

theorem binder_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (hne : tag ≠ 2)
    (w mode depth parameter s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (he : Derives Γ (binderCase tag w mode depth parameter n q)) : Derives Γ .bot := by
  let B := binderBody tag w mode depth parameter n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc s.castSucc x.castSucc y.castSucc n.castSucc) := of_eq (SyntaxAtomSyntax.memberCode_rename w s x y n Fin.castSucc) (under hn B)
  exact unary_rejected (ZFContext.under hZ B) tag hne w.castSucc mode.castSucc (Fin.last m) parameter.castSucc s.castSucc x.castSucc y.castSucc n.castSucc q.castSucc hw1 hn1 (.conjR (.hyp (Or.inl rfl)))

theorem outcomes_iff_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n)) :
    Derives Γ ((OriginalFormulaTraceEquation.outcomes w mode depth parameter n q).iff
      (applicationCase w mode depth parameter n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalFormulaTraceEquation.outcomes w mode depth parameter n q
    have hZ0 := ZFContext.add hZ E
    have hw0 := add hw E
    have hn0 := add hn E
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .botE (constant_rejected (ZFContext.add hZ0 _) 0 (by decide) w s x y n q (add hw0 _) (add hn0 _) (.hyp (Or.inl rfl)))
    · let Tail0 := (OriginalFormulaLocalData.constant 1 w n q).disj ((applicationCase w mode depth parameter n q).disj ((binaryCase 3 1 w mode depth parameter n q).disj ((unaryCase 4 w mode depth parameter n q).disj ((binaryCase 5 3 w mode depth parameter n q).disj ((binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot))))))))))
      have hZ1 := ZFContext.add hZ0 Tail0
      have hw1 := add hw0 Tail0
      have hn1 := add hn0 Tail0
      apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .botE (constant_rejected (ZFContext.add hZ1 _) 1 (by decide) w s x y n q (add hw1 _) (add hn1 _) (.hyp (Or.inl rfl)))
      · let Tail1 := (applicationCase w mode depth parameter n q).disj ((binaryCase 3 1 w mode depth parameter n q).disj ((unaryCase 4 w mode depth parameter n q).disj ((binaryCase 5 3 w mode depth parameter n q).disj ((binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot)))))))))
        have hZ2 := ZFContext.add hZ1 Tail1
        have hw2 := add hw1 Tail1
        have hn2 := add hn1 Tail1
        apply Derives.disjE (.hyp (Or.inl rfl))
        · exact .hyp (Or.inl rfl)
        · let Tail2 := (binaryCase 3 1 w mode depth parameter n q).disj ((unaryCase 4 w mode depth parameter n q).disj ((binaryCase 5 3 w mode depth parameter n q).disj ((binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot))))))))
          have hZ3 := ZFContext.add hZ2 Tail2
          have hw3 := add hw2 Tail2
          have hn3 := add hn2 Tail2
          apply Derives.disjE (.hyp (Or.inl rfl))
          · exact .botE (binary_rejected (ZFContext.add hZ3 _) 3 1 (by decide) w mode depth parameter s x y n q (add hw3 _) (add hn3 _) (.hyp (Or.inl rfl)))
          · let Tail3 := (unaryCase 4 w mode depth parameter n q).disj ((binaryCase 5 3 w mode depth parameter n q).disj ((binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot)))))))
            have hZ4 := ZFContext.add hZ3 Tail3
            have hw4 := add hw3 Tail3
            have hn4 := add hn3 Tail3
            apply Derives.disjE (.hyp (Or.inl rfl))
            · exact .botE (unary_rejected (ZFContext.add hZ4 _) 4 (by decide) w mode depth parameter s x y n q (add hw4 _) (add hn4 _) (.hyp (Or.inl rfl)))
            · let Tail4 := (binaryCase 5 3 w mode depth parameter n q).disj ((binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot))))))
              have hZ5 := ZFContext.add hZ4 Tail4
              have hw5 := add hw4 Tail4
              have hn5 := add hn4 Tail4
              apply Derives.disjE (.hyp (Or.inl rfl))
              · exact .botE (binary_rejected (ZFContext.add hZ5 _) 5 3 (by decide) w mode depth parameter s x y n q (add hw5 _) (add hn5 _) (.hyp (Or.inl rfl)))
              · let Tail5 := (binaryCase 6 3 w mode depth parameter n q).disj ((binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot)))))
                have hZ6 := ZFContext.add hZ5 Tail5
                have hw6 := add hw5 Tail5
                have hn6 := add hn5 Tail5
                apply Derives.disjE (.hyp (Or.inl rfl))
                · exact .botE (binary_rejected (ZFContext.add hZ6 _) 6 3 (by decide) w mode depth parameter s x y n q (add hw6 _) (add hn6 _) (.hyp (Or.inl rfl)))
                · let Tail6 := (binaryCase 7 3 w mode depth parameter n q).disj ((binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot))))
                  have hZ7 := ZFContext.add hZ6 Tail6
                  have hw7 := add hw6 Tail6
                  have hn7 := add hn6 Tail6
                  apply Derives.disjE (.hyp (Or.inl rfl))
                  · exact .botE (binary_rejected (ZFContext.add hZ7 _) 7 3 (by decide) w mode depth parameter s x y n q (add hw7 _) (add hn7 _) (.hyp (Or.inl rfl)))
                  · let Tail7 := (binaryCase 8 3 w mode depth parameter n q).disj ((binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot)))
                    have hZ8 := ZFContext.add hZ7 Tail7
                    have hw8 := add hw7 Tail7
                    have hn8 := add hn7 Tail7
                    apply Derives.disjE (.hyp (Or.inl rfl))
                    · exact .botE (binary_rejected (ZFContext.add hZ8 _) 8 3 (by decide) w mode depth parameter s x y n q (add hw8 _) (add hn8 _) (.hyp (Or.inl rfl)))
                    · let Tail8 := (binderCase 9 w mode depth parameter n q).disj ((binderCase 10 w mode depth parameter n q).disj (Formula.bot))
                      have hZ9 := ZFContext.add hZ8 Tail8
                      have hw9 := add hw8 Tail8
                      have hn9 := add hn8 Tail8
                      apply Derives.disjE (.hyp (Or.inl rfl))
                      · exact .botE (binder_rejected (ZFContext.add hZ9 _) 9 (by decide) w mode depth parameter s x y n q (add hw9 _) (add hn9 _) (.hyp (Or.inl rfl)))
                      · let Tail9 := (binderCase 10 w mode depth parameter n q).disj (Formula.bot)
                        have hZ10 := ZFContext.add hZ9 Tail9
                        have hw10 := add hw9 Tail9
                        have hn10 := add hn9 Tail9
                        apply Derives.disjE (.hyp (Or.inl rfl))
                        · exact .botE (binder_rejected (ZFContext.add hZ10 _) 10 (by decide) w mode depth parameter s x y n q (add hw10 _) (add hn10 _) (.hyp (Or.inl rfl)))
                        · exact .botE (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact .disjR (.disjR (.disjL (.hyp (Or.inl rfl))))

theorem run_iff_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff
      (applicationCase w mode depth parameter n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaRunEquation.run_iff hZ three w mode depth parameter n q hw hm hd hp)
    (outcomes_iff_application hZ w mode depth parameter s x y n q hw hn)

end PPAC.Migration.Internal.OriginalMemberRunDispatch
