import PPAC.Migration.Internal.SyntaxUnaryIterationCore

/-! Exact zero and unary-constructor successor equations, at arbitrary internal counts. -/
namespace PPAC.Migration.Internal.SyntaxUnaryIterationLaws
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxUnaryIterationSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hz : Derives Γ (empty z)) : Derives Γ (iterate tag w a z a) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hy := SyntaxUnaryIterationCore.exists_iteration hZ tag w a z hw ha hzW
  let Y := (Formula.mem (Fin.last m) w.castSucc).conj (iterate tag w.castSucc a.castSucc z.castSucc (Fin.last m))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) hy
  have hzY := of_eq (empty_rename z Fin.castSucc) (under hz Y)
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have heq := NaturalRecursionLaws.evaluation_zero (SyntaxUnaryIterationStep.matrix tag) (params w.castSucc)
    w.castSucc a.castSucc z.castSucc (Fin.last m) hzY (.conjR hY)
  exact of_eq (by simp only [Formula.raise, iterate_rename])
    (output_subst tag w.castSucc a.castSucc z.castSucc (Fin.last m) a.castSucc heq (.conjR hY))

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a z y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((iterate tag w a z y).iff (.equal y a)) := by
  have hi := zero_value hZ tag w a z hw ha hz
  apply Derives.conjI
  · apply Derives.impI
    exact NaturalRecursionLaws.evaluation_zero (SyntaxUnaryIterationStep.matrix tag) (params w) w a z y (add hz _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact output_subst tag w a z a y (eq_symm (.hyp (Or.inl rfl))) (add hi _)

theorem successor_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a n s y z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (iterate tag w a n y)) (hz : Derives Γ (iterate tag w a s z)) :
    Derives Γ (SyntaxNodeSyntax.constructor 1 tag w (fun _ => y) z) := by
  have hyW := SyntaxUnaryIterationCore.range hZ tag w a n y hw ha hy
  have hrel := NaturalEvaluationStep.evaluation_step (ZFContext.arithmetic hZ) (SyntaxUnaryIterationStep.matrix tag) (params w)
    w a n s y z hw hn hs
    (OmegaOrdinals.elements w (ZFContext.arithmetic hZ).base.foundation (ZFContext.arithmetic hZ).ordinalSeparation hw)
    (SyntaxUnaryIterationCore.recursors hZ tag w a hw) hy hz
  exact SyntaxUnaryIterationStep.on_natural tag w y z hyW
    (of_eq (SyntaxUnaryIterationStep.matrix_rel tag (params w) y z) hrel)

theorem successor_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a n s y z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (iterate tag w a n y))
    (hz : Derives Γ (SyntaxNodeSyntax.constructor 1 tag w (fun _ => y) z)) : Derives Γ (iterate tag w a s z) := by
  have hsW := OmegaStructureAlgebra.successor_member w s n (ZFContext.arithmetic hZ).base.extensionality hw hn hs
  have ht := SyntaxUnaryIterationCore.exists_iteration hZ tag w a s hw ha hsW
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (iterate tag w.castSucc a.castSucc s.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) ht
  have hZT := ZFContext.under hZ T
  have hwT := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hsT := of_eq (successor_rename s n Fin.castSucc) (under hs T)
  have hyT := of_eq (iterate_rename tag w a n y Fin.castSucc) (under hy T)
  have hzT := of_eq (SyntaxNodeSyntax.constructor_rename 1 tag w (fun _ => y) z Fin.castSucc) (under hz T)
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hty := successor_forward hZT tag w.castSucc a.castSucc n.castSucc s.castSucc y.castSucc (Fin.last m)
    hwT (under ha T) (under hn T) hsT hyT (.conjR hT)
  have heq := SyntaxConstructors.unique hZT 1 tag w.castSucc (fun _ => y.castSucc) (Fin.last m) z.castSucc hwT hty hzT
  exact of_eq (by simp only [Formula.raise, iterate_rename])
    (output_subst tag w.castSucc a.castSucc s.castSucc (Fin.last m) z.castSucc heq (.conjR hT))

theorem successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a n s y z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (iterate tag w a n y)) :
    Derives Γ ((iterate tag w a s z).iff (SyntaxNodeSyntax.constructor 1 tag w (fun _ => y) z)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact successor_forward (ZFContext.add hZ _) tag w a n s y z (add hw _) (add ha _) (add hn _) (add hs _) (add hy _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact successor_backward (ZFContext.add hZ _) tag w a n s y z (add hw _) (add ha _) (add hn _) (add hs _) (add hy _) (.hyp (Or.inl rfl))

theorem all_internal_counts {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (fiber tag w.castSucc a.castSucc (Fin.last m)))) := by
  apply Derives.allI
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have ha1 := Derives.rename Fin.castSucc ha
  apply Derives.impI
  exact SyntaxUnaryIterationCore.exists_unique (ZFContext.add (ZFContext.rename hZ Fin.castSucc) _) tag
    w.castSucc a.castSucc (Fin.last m) (add hw1 _) (add ha1 _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxUnaryIterationLaws
