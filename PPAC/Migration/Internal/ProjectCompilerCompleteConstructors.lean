import PPAC.Migration.Internal.ProjectCompilerCompleteIntro

/-! Actual logical output codes are constructed inside object existential quantifiers. -/
namespace PPAC.Migration.Internal.ProjectCompilerCompleteConstructors
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerCompleteSyntax ProjectCompilerRecursiveSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem single_cases {m} {Γ : Context m} (tag : Nat) (advance : Bool)
    (hs : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w b z n q : Fin m)
    (hc : Derives Γ (ProjectCompilerCaseSyntax.singleCase tag advance codeMatrix (parameters w) w b n q)) :
    Derives Γ (casesAt w b z n q) := by
  rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc)))))))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR hc)))))))))))

theorem binary_cases {m} {Γ : Context m} (kind : Fin 4) (w b z n q : Fin m)
    (hc : Derives Γ (ProjectCompilerCaseSyntax.binaryCase kind codeMatrix (parameters w) w b n q)) :
    Derives Γ (casesAt w b z n q) := by
  rcases kind with ⟨i,hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc)))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc))))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc)))))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hc))))))))))

theorem single_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (hs : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w n b z x y : Fin m) (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n))
    (hc : Derives Γ (ProjectCompilerCaseSyntax.check advance codeMatrix (parameters w) n x b y)) :
    Derives Γ (existsOutput w n b) := by
  have hn := SyntaxNodeInjective.constructor_range hZ 1 tag w (fun _ => x) n hw hd
  have hy := ProjectCompilerCompleteIntro.check_output_natural advance w n x b y hc
  have hi : Derives Γ (SyntaxForestSyntax.inputs 1 w (fun _ => y)) := .conjI hy (.eqRefl w)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxLogicalSyntax.singleCode tag w.castSucc y.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor hZ 1 tag w (fun _ => y) hw hi)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hb1 : Derives Δ (.mem b.castSucc w.castSucc) := under hb B
  have hn1 : Derives Δ (.mem n.castSucc w.castSucc) := under hn B
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz B)
  have hd1 := of_eq (SyntaxLogicalSyntax.singleCode_rename tag w x n Fin.castSucc) (under hd B)
  have hc1 := of_eq (ProjectCompilerCaseSyntax.check_rename advance codeMatrix (parameters w) n x b y Fin.castSucc) (under hc B)
  have hm := ProjectCompilerCaseIntro.single_case tag advance codeMatrix (parameters w.castSucc)
    w.castSucc b.castSucc n.castSucc (Fin.last m) x.castSucc y.castSucc (.conjI hd1 (.conjI hc1 (.conjR hB)))
  have ha := single_cases tag advance hs w.castSucc b.castSucc z.castSucc n.castSucc (Fin.last m) hm
  have hp := ProjectCompilerCompleteIntro.of_cases (ZFContext.under hZ B) w.castSucc n.castSucc b.castSucc (Fin.last m) z.castSucc
    hw1 hn1 hb1 (.conjL hB) hz1 ha
  exact of_eq (existsOutput_rename w n b Fin.castSucc).symm (intro_output w.castSucc n.castSucc b.castSucc (Fin.last m) hp)

theorem binary_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w n b z x y X Y : Fin m) (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hd : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hX : Derives Γ (ProjectCompilerCaseSyntax.queried codeMatrix (parameters w) n x b X))
    (hY : Derives Γ (ProjectCompilerCaseSyntax.queried codeMatrix (parameters w) n y b Y)) :
    Derives Γ (existsOutput w n b) := by
  have hn := SyntaxNodeInjective.constructor_range hZ 2 (SyntaxLogicalSyntax.binaryTag kind) w (SyntaxAtomSyntax.two x y) n hw hd
  have hx := ProjectCompilerCompleteIntro.query_output_natural w n x b X hX
  have hy := ProjectCompilerCompleteIntro.query_output_natural w n y b Y hY
  have hi : Derives Γ (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two X Y)) := .conjI hx (.conjI hy (.eqRefl w))
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxLogicalSyntax.binaryCode kind w.castSucc X.castSucc Y.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor hZ 2 (SyntaxLogicalSyntax.binaryTag kind) w (SyntaxAtomSyntax.two X Y) hw hi)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hb1 : Derives Δ (.mem b.castSucc w.castSucc) := under hb B
  have hn1 : Derives Δ (.mem n.castSucc w.castSucc) := under hn B
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz B)
  have hd1 := of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w x y n Fin.castSucc) (under hd B)
  have hX1 := of_eq (ProjectCompilerCaseSyntax.queried_rename codeMatrix (parameters w) n x b X Fin.castSucc) (under hX B)
  have hY1 := of_eq (ProjectCompilerCaseSyntax.queried_rename codeMatrix (parameters w) n y b Y Fin.castSucc) (under hY B)
  have hm := ProjectCompilerCaseIntro.binary_case kind codeMatrix (parameters w.castSucc)
    w.castSucc b.castSucc n.castSucc (Fin.last m) x.castSucc y.castSucc X.castSucc Y.castSucc
    (.conjI hd1 (.conjI hX1 (.conjI hY1 (.conjR hB))))
  have ha := binary_cases kind w.castSucc b.castSucc z.castSucc n.castSucc (Fin.last m) hm
  have hp := ProjectCompilerCompleteIntro.of_cases (ZFContext.under hZ B) w.castSucc n.castSucc b.castSucc (Fin.last m) z.castSucc
    hw1 hn1 hb1 (.conjL hB) hz1 ha
  exact of_eq (existsOutput_rename w n b Fin.castSucc).symm (intro_output w.castSucc n.castSucc b.castSucc (Fin.last m) hp)

end PPAC.Migration.Internal.ProjectCompilerCompleteConstructors
