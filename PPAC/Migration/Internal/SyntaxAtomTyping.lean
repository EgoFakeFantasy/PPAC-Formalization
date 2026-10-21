import PPAC.Migration.Internal.SyntaxZeroScalar

/-! 已知原子构造码的类型双条件；实际解码恢复所有字段并检查同一内部上下文。 -/
namespace PPAC.Migration.Internal.SyntaxAtomTyping
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxAtomLogic
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nullary_iff_contexts {m} {Γ : Context m} (truth : Bool) (w b f n : Fin m)
    (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n)) : Derives Γ ((nullary truth w b f n).iff (contexts w b f)) := by
  apply Derives.conjI
  · exact .impI (.conjL (.hyp (Or.inl rfl)))
  · exact .impI (.conjI (.hyp (Or.inl rfl)) (add hc _))

theorem false_iff_two {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((nullary false w b f n).iff ((contexts w b f).conj (SyntaxNumeralSyntax.numeral 2 n))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hn : Derives (Context.add (nullary false w b f n) Γ) (nullary false w b f n) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hn) (SyntaxZeroScalar.to_numeral_two (ZFContext.add hZ _) _ _ (add hw _) (.conjR hn))
  · apply Derives.impI
    have hn : Derives (Context.add ((contexts w b f).conj (SyntaxNumeralSyntax.numeral 2 n)) Γ)
        ((contexts w b f).conj (SyntaxNumeralSyntax.numeral 2 n)) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hn) (SyntaxZeroScalar.from_numeral_two (ZFContext.add hZ _) _ _ (add hw _) (.conjR hn))

theorem member_types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f s x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (memberCode w s x y n)) (hm : Derives Γ (membership w b f n)) : Derives Γ (memberTypes w b f s x y) := by
  let B := memberBody w b f n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_member w b f n _ hm
  have hZ3 : ZFContext.Evidence Δ := zf_under_three hZ B
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_three hw B
  have hc3 : Derives Δ (memberCode w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, memberCode_rename] using under_three hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hsEq := SyntaxNodeInjective.constructor_input_eq hZ3 3 2 2 _ _ _ _ 0 hw3 (.conjR hB) hc3
  have hxEq := SyntaxNodeInjective.constructor_input_eq hZ3 3 2 2 _ _ _ _ 1 hw3 (.conjR hB) hc3
  have hyEq := SyntaxNodeInjective.constructor_input_eq hZ3 3 2 2 _ _ _ _ 2 hw3 (.conjR hB) hc3
  have hs := zeroScalar_output_subst _ _ _ hsEq (.conjL (.conjL hB))
  have hx := term_output_subst _ _ _ _ _ hxEq (.conjL (.conjR (.conjL hB)))
  have hy := term_output_subst _ _ _ _ _ hyEq (.conjR (.conjR (.conjL hB)))
  have hout : Derives Δ (memberTypes w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc
      s.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc) := .conjI hs (.conjI hx hy)
  simpa only [Formula.raise, memberTypes_rename] using hout

theorem member_iff_types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f s x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (memberCode w s x y n)) : Derives Γ ((membership w b f n).iff (memberTypes w b f s x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact member_types (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hw _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_member _ _ _ _ _ _ _ (.conjI (.hyp (Or.inl rfl)) (add hc _))

theorem equal_types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (equalCode w x y n)) (hm : Derives Γ (equality w b f n)) : Derives Γ (equalTypes w b f x y) := by
  let B := equalBody w b f n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_equality w b f n _ hm
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw B
  have hc2 : Derives Δ (equalCode w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, equalCode_rename] using OrderedPairElimination.under_two hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hxEq := SyntaxNodeInjective.constructor_input_eq hZ2 2 3 3 _ _ _ _ 0 hw2 (.conjR hB) hc2
  have hyEq := SyntaxNodeInjective.constructor_input_eq hZ2 2 3 3 _ _ _ _ 1 hw2 (.conjR hB) hc2
  have hx := term_output_subst _ _ _ _ _ hxEq (.conjL (.conjL hB))
  have hy := term_output_subst _ _ _ _ _ hyEq (.conjR (.conjL hB))
  have hout : Derives Δ (equalTypes w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc) := .conjI hx hy
  simpa only [Formula.raise, equalTypes_rename] using hout

theorem equal_iff_types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (equalCode w x y n)) : Derives Γ ((equality w b f n).iff (equalTypes w b f x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact equal_types (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_equality _ _ _ _ _ _ (.conjI (.hyp (Or.inl rfl)) (add hc _))
end PPAC.Migration.Internal.SyntaxAtomTyping
