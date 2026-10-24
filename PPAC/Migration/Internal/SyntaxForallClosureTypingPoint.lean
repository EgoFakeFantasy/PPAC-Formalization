import PPAC.Migration.Internal.SyntaxForallClosureTypingHelpers

/-! Pointwise zero and successor typing, with changing remaining scope in the IH. -/
namespace PPAC.Migration.Internal.SyntaxForallClosureTypingPoint
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForallClosureTypingSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a source f n b y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (empty n)) (hb : Derives Γ (.mem b w))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w n b source))
    (hy : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a n y)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w y b f).iff (FormulaCodeSyntax.formulaCode w a source f)) := by
  have es := SyntaxForallClosureTypingHelpers.zero_sum hZ w n b source hw hn hb hs
  have ey := NaturalRecursionLaws.evaluation_zero (SyntaxUnaryIterationStep.matrix 9) (SyntaxUnaryIterationSyntax.params w) w a n y hn hy
  apply Derives.conjI
  · apply Derives.impI
    exact FormulaCodeTransport.code_bound w a b f source (add (eq_symm es) _)
      (FormulaCodeTransport.code_root w y b f a (add ey _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact FormulaCodeTransport.code_root w a b f y (add (eq_symm ey) _)
      (FormulaCodeTransport.code_bound w a source f b (add es _) (.hyp (Or.inl rfl)))

theorem step_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a source f n s b y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hf : Derives Γ (.mem f w))
    (hn : Derives Γ (.mem n w)) (hi : Derives Γ (correct w a source f n))
    (hs : Derives Γ (successor s n)) (hb : Derives Γ (.mem b w))
    (ht : Derives Γ (NaturalAdditionSyntax.sum w s b source))
    (hy : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a s y)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w y b f).iff (FormulaCodeSyntax.formulaCode w a source f)) := by
  let C := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) b.castSucc)
  let Γ1 := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) (Derives.impE (OmegaSyntax.step_at w b (.conjL hw)) hb)
  have hZ1 := ZFContext.under hZ C
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw C)
  let U := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (SyntaxUnaryIterationSyntax.iterate 9 w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)))
  let Γ2 := Context.add U (Context.image Formula.raise Γ1)
  apply Derives.exE (p := U) (SyntaxUnaryIterationCore.exists_iteration hZ1 9 w.castSucc a.castSucc n.castSucc hw1 (under ha C) (under hn C))
  have hZ2 := ZFContext.under hZ1 U
  have R {p : Formula m} (hp : Derives Γ p) := under (under hp C) U
  have hw2 : Derives Γ2 (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (R hw)
  have ha2 : Derives Γ2 (.mem a.castSucc.castSucc w.castSucc.castSucc) := R ha
  have hf2 : Derives Γ2 (.mem f.castSucc.castSucc w.castSucc.castSucc) := R hf
  have hn2 : Derives Γ2 (.mem n.castSucc.castSucc w.castSucc.castSucc) := R hn
  have hb2 : Derives Γ2 (.mem b.castSucc.castSucc w.castSucc.castSucc) := R hb
  have hs2 : Derives Γ2 (successor s.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (R hs)
  have ht2 : Derives Γ2 (NaturalAdditionSyntax.sum w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc source.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, NaturalAdditionSyntax.sum_rename]) (R ht)
  have hy2 : Derives Γ2 (SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc a.castSucc.castSucc s.castSucc.castSucc y.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxUnaryIterationSyntax.forallClosure_rename]) (R hy)
  have hi2 : Derives Γ2 (correct w.castSucc.castSucc a.castSucc.castSucc source.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, correct_rename]) (R hi)
  have hC : Derives Γ1 C := .hyp (Or.inl rfl)
  have hC2 : Derives Γ2 ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (successor (Fin.last m).castSucc b.castSucc.castSucc)) :=
    of_eq (by simp only [C, Formula.raise, Formula.rename, successor_rename]) (under hC U)
  have hU : Derives Γ2 U := .hyp (Or.inl rfl)
  have hsum := SyntaxForallClosureTypingHelpers.move_successor hZ2 w.castSucc.castSucc n.castSucc.castSucc s.castSucc.castSucc
    b.castSucc.castSucc (Fin.last m).castSucc source.castSucc.castSucc hw2 hn2 hb2 hs2 (.conjR hC2) ht2
  have ih := at_point w.castSucc.castSucc a.castSucc.castSucc source.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hi2 (.conjL hC2) hsum (.conjR hU)
  have hnode := SyntaxUnaryIterationLaws.successor_forward hZ2 9 w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc
    s.castSucc.castSucc (Fin.last (m+1)) y.castSucc.castSucc hw2 ha2 hn2 hs2 (.conjR hU) hy2
  have hq := SyntaxForallClosureTypingHelpers.quantified_at_successor hZ2 w.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc
    f.castSucc.castSucc (Fin.last (m+1)) y.castSucc.castSucc hw2 hb2 hf2 (.conjR hC2) hnode
  have ho : Derives Γ2 ((FormulaCodeSyntax.formulaCode w.castSucc.castSucc y.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc).iff
      (FormulaCodeSyntax.formulaCode w.castSucc.castSucc a.castSucc.castSucc source.castSucc.castSucc f.castSucc.castSucc)) := by
    apply Derives.conjI
    · apply Derives.impI
      exact .impE (add (.conjL ih) _) (.impE (add (.conjL hq) _) (.hyp (Or.inl rfl)))
    · apply Derives.impI
      exact .impE (add (.conjR hq) _) (.impE (add (.conjR ih) _) (.hyp (Or.inl rfl)))
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, FormulaCodeSyntax.formulaCode_rename]) ho

end PPAC.Migration.Internal.SyntaxForallClosureTypingPoint
