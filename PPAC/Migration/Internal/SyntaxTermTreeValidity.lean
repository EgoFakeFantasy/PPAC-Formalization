import PPAC.Migration.Internal.SyntaxTreeValidity

/-! 原scalar、bvar/fvar及完整纯项的原树有效性；内部变量索引没有外部界。 -/
namespace PPAC.Migration.Internal.SyntaxTermTreeValidity
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTreeValiditySyntax StructuralTreeValiditySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem variable_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w i n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxVariableSyntax.code bound w i n)) : Derives Γ (valid w n) := by
  let C := SyntaxVariableSyntax.codeBody bound w i n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply SyntaxVariableSyntax.eliminate_code bound w i n _ hc
  have hZ1 := ZFContext.under hZ C
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hs := SyntaxTreeValidity.scalar hZ1 w.castSucc i.castSucc (Fin.last m) hw1 (.conjL hC)
  have hout := SyntaxTreeValidity.constructor hZ1 1 (SyntaxVariableSyntax.tag bound) w.castSucc (fun _ => Fin.last m) n.castSucc
    hw1 (.conjR hC) (.conjI hs (.eqRefl w.castSucc))
  simpa only [Formula.raise, valid_rename] using hout

theorem branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w l n : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxTermSyntax.branch bound w l n)) : Derives Γ (valid w n) := by
  let B := SyntaxTermSyntax.branchWitness bound w l n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch bound w l n _ hb
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := variable_code (ZFContext.under hZ B) bound w.castSucc (Fin.last m) n.castSucc hw1 (.conjR hB)
  simpa only [Formula.raise, valid_rename] using hout

theorem term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxTermSyntax.term w b f n)) : Derives Γ (valid w n) := by
  apply Derives.disjE (.conjR ht)
  · exact branch (ZFContext.add hZ _) true w b n (add hw _) (.hyp (Or.inl rfl))
  · exact branch (ZFContext.add hZ _) false w f n (add hw _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxTermTreeValidity
