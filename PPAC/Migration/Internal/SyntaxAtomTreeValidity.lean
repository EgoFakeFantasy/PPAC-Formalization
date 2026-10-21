import PPAC.Migration.Internal.FormulaCodeTreeValiditySyntax

/-! 原四种原子公式的树有效性；全部真实符号/项字段均实际处理。 -/
namespace PPAC.Migration.Internal.SyntaxAtomTreeValidity
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxAtomSyntax SyntaxTreeValiditySyntax StructuralTreeValiditySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.nullary truth w b f n)) : Derives Γ (valid w n) :=
  SyntaxTreeValidity.constructor hZ 0 (nullaryTag truth) w Fin.elim0 n hw (.conjR hc) (.eqRefl w)

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.membership w b f n)) : Derives Γ (valid w n) := by
  let C := memberBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply SyntaxAtomLogic.eliminate_member w b f n _ hc
  have hZ3 := SyntaxAtomLogic.zf_under_three hZ C
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using SyntaxAtomLogic.under_three hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have ht := Derives.conjL hC
  have hs := SyntaxTreeValidity.constructor hZ3 0 0 w.castSucc.castSucc.castSucc Fin.elim0
    (Fin.last m).castSucc.castSucc hw3 (.conjL ht) (.eqRefl w.castSucc.castSucc.castSucc)
  have hx := SyntaxTermTreeValidity.term hZ3 w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc hw3 (.conjL (.conjR ht))
  have hy := SyntaxTermTreeValidity.term hZ3 w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc
    (Fin.last (m+2)) hw3 (.conjR (.conjR ht))
  have hin : Derives Δ (validInputs 3 w.castSucc.castSucc.castSucc
      (three (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))) :=
    .conjI hs (.conjI hx (.conjI hy (.eqRefl w.castSucc.castSucc.castSucc)))
  have hout := SyntaxTreeValidity.constructor hZ3 3 2 _ _ _ hw3 (.conjR hC) hin
  simpa only [Formula.raise, valid_rename] using hout

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.equality w b f n)) : Derives Γ (valid w n) := by
  let C := equalBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxAtomLogic.eliminate_equality w b f n _ hc
  have hZ2 := ZFContext.under_two hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have ht := Derives.conjL hC
  have hx := SyntaxTermTreeValidity.term hZ2 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc
    (Fin.last m).castSucc hw2 (.conjL ht)
  have hy := SyntaxTermTreeValidity.term hZ2 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc
    (Fin.last (m+1)) hw2 (.conjR ht)
  have hin : Derives Δ (validInputs 2 w.castSucc.castSucc (two (Fin.last m).castSucc (Fin.last (m+1)))) :=
    .conjI hx (.conjI hy (.eqRefl w.castSucc.castSucc))
  have hout := SyntaxTreeValidity.constructor hZ2 2 3 _ _ _ hw2 (.conjR hC) hin
  simpa only [Formula.raise, valid_rename] using hout

theorem atomic {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.atomic w b f n)) : Derives Γ (valid w n) := by
  apply Derives.disjE hc
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact nullary (ZFContext.add (ZFContext.add hZ _) _) false w b f n (add (add hw _) _) (.hyp (Or.inl rfl))
    · exact nullary (ZFContext.add (ZFContext.add hZ _) _) true w b f n (add (add hw _) _) (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact membership (ZFContext.add (ZFContext.add hZ _) _) w b f n (add (add hw _) _) (.hyp (Or.inl rfl))
    · exact equality (ZFContext.add (ZFContext.add hZ _) _) w b f n (add (add hw _) _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxAtomTreeValidity
