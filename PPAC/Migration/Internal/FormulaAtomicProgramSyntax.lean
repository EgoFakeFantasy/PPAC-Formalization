import PPAC.Migration.Internal.FormulaTransformProgramSyntax
import PPAC.Migration.Internal.HornBinderRules

/-! 四类原子组成实际既有公式程序的有限子程序；输入类型由原受检调用恢复。 -/
namespace PPAC.Migration.Internal.FormulaAtomicProgramSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaTransformProgramSyntax (Program)

def program : Program := .either
  (.either (.branch (.nullary false)) (.branch (.nullary true)))
  (.either (.branch .membership) (.branch .equality))

def run {m} (w R S a b c d n q : Fin m) : Formula m :=
  ((FormulaTransformAtomSyntax.nullary false w a b c d n q).disj
    (FormulaTransformAtomSyntax.nullary true w a b c d n q)).disj
      ((FormulaTransformAtomSyntax.membership w R S a b c d n q).disj
        (FormulaTransformAtomSyntax.equality w R S a b c d n q))

theorem run_eq_program {m} (w R S a b c d h n q : Fin m) :
    run w R S a b c d n q = FormulaTransformProgramSyntax.run program w R S a b c d h n q := rfl

theorem run_rename {m j} (w R S a b c d n q : Fin m) (ρ : Fin m → Fin j) :
    (run w R S a b c d n q).rename ρ = run (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [run, Formula.rename, FormulaTransformAtomSyntax.nullary_rename, FormulaTransformAtomSyntax.membership_rename, FormulaTransformAtomSyntax.equality_rename]

theorem membership_source {m} {Γ : Context m} (w R S a b c d n q : Fin m)
    (hr : Derives Γ (FormulaTransformAtomSyntax.membership w R S a b c d n q)) :
    Derives Γ (SyntaxAtomSyntax.membership w a b n) := by
  let B := FormulaTransformAtomSyntax.membershipBody w R S a b c d n q
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 B _ hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := Derives.conjR (Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hB)))))
  have hy := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hB)))))
  have hs := SyntaxAtomLogic.intro_member (old 5 w) (old 5 a) (old 5 b) (slot 5 0) (slot 5 1) (slot 5 2) (old 5 n)
    (.conjI (.conjI (.conjL hB) (.conjI hx hy)) (.conjL (.conjR hB)))
  exact of_eq (SyntaxAtomSyntax.membership_rename w a b n (old 5)).symm hs

theorem equality_source {m} {Γ : Context m} (w R S a b c d n q : Fin m)
    (hr : Derives Γ (FormulaTransformAtomSyntax.equality w R S a b c d n q)) :
    Derives Γ (SyntaxAtomSyntax.equality w a b n) := by
  let B := FormulaTransformAtomSyntax.equalityBody w R S a b c d n q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := Derives.conjR (Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR hB))))
  have hy := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hB))))
  have hs := SyntaxAtomLogic.intro_equality (old 4 w) (old 4 a) (old 4 b) (slot 4 0) (slot 4 1) (old 4 n)
    (.conjI (.conjI hx hy) (.conjL hB))
  exact of_eq (SyntaxAtomSyntax.equality_rename w a b n (old 4)).symm hs

theorem source {m} {Γ : Context m} (w R S a b c d n q : Fin m)
    (hr : Derives Γ (run w R S a b c d n q)) : Derives Γ (SyntaxAtomSyntax.atomic w a b n) := by
  apply Derives.disjE hr
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjL (.disjL (.conjL (.hyp (Or.inl rfl))))
    · exact .disjL (.disjR (.conjL (.hyp (Or.inl rfl))))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjR (.disjL (membership_source w R S a b c d n q (.hyp (Or.inl rfl))))
    · exact .disjR (.disjR (equality_source w R S a b c d n q (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.FormulaAtomicProgramSyntax
