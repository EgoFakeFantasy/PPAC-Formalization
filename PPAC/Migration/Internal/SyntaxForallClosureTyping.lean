import PPAC.Migration.Internal.SyntaxForallClosureTypingPoint

/-! Object omega induction discharges the typing IH for all internal closure counts. -/
namespace PPAC.Migration.Internal.SyntaxForallClosureTyping
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax OriginalUniversalBlock SyntaxForallClosureTypingSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem parameter_0 {m} (w a source f : Fin m) : parameters w a source f 0 = w := rfl

theorem parameter_1 {m} (w a source f : Fin m) : parameters w a source f 1 = a := rfl

theorem parameter_2 {m} (w a source f : Fin m) : parameters w a source f 2 = source := rfl

theorem parameter_3 {m} (w a source f : Fin m) : parameters w a source f 3 = f := rfl

theorem zero_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a source f n : Fin m)
    (hw : Derives Γ (omega w))
    (hz : Derives Γ (empty n))
    : Derives Γ (correct w a source f n) := by
  apply OriginalUniversalBlock.intro_many 2 (body w a source f n)
  let Δ := raisedContext 2 Γ
  have hZ2 := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have R {p : Formula m} (hp : Derives Γ p) := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [omega_rename]) (R hw)
  have hz2 : Derives Δ (empty n.castSucc.castSucc) := of_eq (by simp only [empty_rename]) (R hz)
  change Derives Δ (correctAt w.castSucc.castSucc a.castSucc.castSucc source.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (slot 2 0) (slot 2 1))
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact SyntaxForallClosureTypingPoint.zero_point (ZFContext.add (ZFContext.add (ZFContext.add hZ2 _) _) _) w.castSucc.castSucc a.castSucc.castSucc source.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (slot 2 0) (slot 2 1)
    (add (add (add hw2 _) _) _) (add (add (add hz2 _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem step_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a source f n s : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (.mem a w))
    (hf : Derives Γ (.mem f w))
    (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (correct w a source f n))
    (hs : Derives Γ (successor s n))
    : Derives Γ (correct w a source f s) := by
  apply OriginalUniversalBlock.intro_many 2 (body w a source f s)
  let Δ := raisedContext 2 Γ
  have hZ2 := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have R {p : Formula m} (hp : Derives Γ p) := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [omega_rename]) (R hw)
  have ha2 : Derives Δ (.mem a.castSucc.castSucc w.castSucc.castSucc) := R ha
  have hf2 : Derives Δ (.mem f.castSucc.castSucc w.castSucc.castSucc) := R hf
  have hn2 : Derives Δ (.mem n.castSucc.castSucc w.castSucc.castSucc) := R hn
  have hi2 : Derives Δ (correct w.castSucc.castSucc a.castSucc.castSucc source.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [correct_rename]) (R hi)
  have hs2 : Derives Δ (successor s.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [successor_rename]) (R hs)
  change Derives Δ (correctAt w.castSucc.castSucc a.castSucc.castSucc source.castSucc.castSucc f.castSucc.castSucc s.castSucc.castSucc (slot 2 0) (slot 2 1))
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact SyntaxForallClosureTypingPoint.step_point (ZFContext.add (ZFContext.add (ZFContext.add hZ2 _) _) _) w.castSucc.castSucc a.castSucc.castSucc source.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc s.castSucc.castSucc (slot 2 0) (slot 2 1)
    (add (add (add hw2 _) _) _) (add (add (add ha2 _) _) _) (add (add (add hf2 _) _) _) (add (add (add hn2 _) _) _) (add (add (add hi2 _) _) _) (add (add (add hs2 _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a source f : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (OmegaInductionSyntax.base SyntaxForallClosureTypingSyntax.matrix (parameters w a source f)) := by
  simp only [OmegaInductionSyntax.base, SyntaxForallClosureTypingSyntax.matrix_pred, paramsUp, parameter_0, parameter_1, parameter_2, parameter_3]
  apply Derives.allI
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  apply Derives.impI
  exact zero_property (ZFContext.add (ZFContext.rename hZ Fin.castSucc) _) w.castSucc a.castSucc source.castSucc f.castSucc
    (Fin.last m) (add hw1 _) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a source f : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hf : Derives Γ (.mem f w)) :
    Derives Γ (OmegaInductionSyntax.step SyntaxForallClosureTypingSyntax.matrix (parameters w a source f) w) := by
  simp only [OmegaInductionSyntax.step, SyntaxForallClosureTypingSyntax.matrix_pred, paramsUp, parameter_0, parameter_1, parameter_2, parameter_3]
  apply Derives.allI
  apply Derives.allI
  have hZ2 := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw2 : Derives (raisedContext 2 Γ) (omega w.castSucc.castSucc) :=
    of_eq (by simp only [omega_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw))
  have ha2 := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha)
  have hf2 := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_property (ZFContext.add (ZFContext.add (ZFContext.add hZ2 _) _) _)
    w.castSucc.castSucc a.castSucc.castSucc source.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add (add (add hw2 _) _) _) (add (add (add ha2 _) _) _) (add (add (add hf2 _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem all_correct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a source f : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hf : Derives Γ (.mem f w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (correct w.castSucc a.castSucc source.castSucc f.castSucc (Fin.last m)))) := by
  have hi := OmegaInduction.induction_on_omega SyntaxForallClosureTypingSyntax.matrix (parameters w a source f) w (ZFContext.separation hZ SyntaxForallClosureTypingSyntax.matrix) hw
    (base hZ w a source f hw) (step hZ w a source f hw ha hf)
  exact of_eq (by simp only [OmegaInductionSyntax.holds, SyntaxForallClosureTypingSyntax.matrix_pred, paramsUp, parameter_0, parameter_1, parameter_2, parameter_3]) hi

theorem at_count {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a source f n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hf : Derives Γ (.mem f w)) (hn : Derives Γ (.mem n w)) :
    Derives Γ (correct w a source f n) := by
  have hi := Derives.allE n (all_correct hZ w a source f hw ha hf)
  have hi' : Derives Γ ((Formula.mem n w).imp (correct w a source f n)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hi
  exact .impE hi' hn

theorem typed_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a source f n b y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hf : Derives Γ (.mem f w))
    (hn : Derives Γ (.mem n w)) (hb : Derives Γ (.mem b w))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w n b source))
    (hy : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a n y)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w y b f).iff (FormulaCodeSyntax.formulaCode w a source f)) :=
  at_point w a source f n b y (at_count hZ w a source f n hw ha hf hn) hb hs hy

end PPAC.Migration.Internal.SyntaxForallClosureTyping
