import PPAC.Migration.Internal.SyntaxCodedMixedTermUnique

/-! 原数值混合环境项替换的实际唯一纤维及准确输入双条件。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedTermFiber
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n)) : Derives Γ (fiber w R S a b c d n) := by
  let Q := substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (SyntaxCodedMixedTermExistence.exists_output hZ w R S a b c d n hw hi)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hu := SyntaxCodedMixedTermUnique.unique_output (ZFContext.under hZ Q) _ _ _ _ _ _ _ _ _ hw1 hQ
  have ho : Derives Δ (fiber w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Q, Formula.instantiate, Formula.rename, substituted_rename, uniqueOutput_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hQ hu)
  exact of_eq (fiber_rename w R S a b c d n Fin.castSucc).symm ho

theorem exists_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsOutput w R S a b c d n).iff (input w R S a b c d n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := existsOutput w R S a b c d n
    let Q := substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := Q) (.hyp (Or.inl rfl))
    have ho := SyntaxCodedMixedTermTyping.input_of_substituted _ _ _ _ _ _ _ _ _ (Derives.hyp (Or.inl rfl) : Derives Δ Q)
    exact of_eq (input_rename w R S a b c d n Fin.castSucc).symm ho
  · apply Derives.impI
    exact SyntaxCodedMixedTermExistence.exists_output (ZFContext.add hZ _) w R S a b c d n (add hw _) (.hyp (Or.inl rfl))

theorem fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((fiber w R S a b c d n).iff (input w R S a b c d n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := fiber w R S a b c d n
    let Q := (substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
      (uniqueOutput w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := Q) (.hyp (Or.inl rfl))
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have ho := SyntaxCodedMixedTermTyping.input_of_substituted _ _ _ _ _ _ _ _ _ (.conjL hQ)
    exact of_eq (input_rename w R S a b c d n Fin.castSucc).symm ho
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) w R S a b c d n (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxCodedMixedTermFiber
