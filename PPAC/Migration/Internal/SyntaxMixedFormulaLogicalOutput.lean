import PPAC.Migration.Internal.SyntaxMixedFormulaLogicalKnown
import PPAC.Migration.Internal.SyntaxMixedFormulaAtomicBase

/-! 七类逻辑原构造的实际唯一输出及六个内部参数Property推进。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaLogicalOutput
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaOutputSyntax SyntaxLogicalSyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n x : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) (hi : Derives Γ (input w R S a b c d n))

    (hc : Derives Γ (singleCode tag w x n)) : Derives Γ (fiber w R S a b c d n) := by
  have hx := SyntaxMixedFormulaLogicalExistence.single_exists hZ tag advance valid w R S a b c d n x hw he hi hc
  let Q := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hx
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hu : Derives Ξ (uniqueOutput w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let V := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Q) V
    have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) Q) V)
    have he2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, earlier_rename]) (under (under (he) Q) V)
    have hc2 : Derives Δ (singleCode tag w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, singleCode_rename]) (under (under (hc) Q) V)
    have hGiven : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [Q, Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) (under hQ V)
    exact SyntaxMixedFormulaLogicalKnown.single_unique hZ2 tag advance valid w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc x.castSucc.castSucc hw2 he2 hc2 (.hyp (Or.inl rfl)) hGiven
  have ho := intro_fiber w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hQ hu
  exact of_eq (fiber_rename w R S a b c d n Fin.castSucc).symm ho

theorem single_property_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w n x : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hc : Derives Γ (singleCode tag w x n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := input w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))
  have hw6 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_6 hw I)
  have he6 : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_6 he I)
  have hc6 : Derives Δ (singleCode tag w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, singleCode_rename]) (under_6 hc I)
  exact single_fiber (zf_under_6 hZ I) tag advance valid w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw6 he6 (.hyp (Or.inl rfl)) hc6

theorem binary_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S a b c d n x y : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) (hi : Derives Γ (input w R S a b c d n))

    (hc : Derives Γ (binaryCode kind w x y n)) : Derives Γ (fiber w R S a b c d n) := by
  have hx := SyntaxMixedFormulaLogicalExistence.binary_exists hZ kind w R S a b c d n x y hw he hi hc
  let Q := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hx
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hu : Derives Ξ (uniqueOutput w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let V := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Q) V
    have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) Q) V)
    have he2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, earlier_rename]) (under (under (he) Q) V)
    have hc2 : Derives Δ (binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, binaryCode_rename]) (under (under (hc) Q) V)
    have hGiven : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [Q, Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) (under hQ V)
    exact SyntaxMixedFormulaLogicalKnown.binary_unique hZ2 kind w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc hw2 he2 hc2 (.hyp (Or.inl rfl)) hGiven
  have ho := intro_fiber w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hQ hu
  exact of_eq (fiber_rename w R S a b c d n Fin.castSucc).symm ho

theorem binary_property_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w n x y : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hc : Derives Γ (binaryCode kind w x y n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := input w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))
  have hw6 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_6 hw I)
  have he6 : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_6 he I)
  have hc6 : Derives Δ (binaryCode kind w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, binaryCode_rename]) (under_6 hc I)
  exact binary_fiber (zf_under_6 hZ I) kind w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw6 he6 (.hyp (Or.inl rfl)) hc6

end PPAC.Migration.Internal.SyntaxMixedFormulaLogicalOutput
