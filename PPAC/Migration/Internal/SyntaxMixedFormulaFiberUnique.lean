import PPAC.Migration.Internal.SyntaxMixedFormulaOutput

/-! 实际输出纤维对所有候选的唯一性；Property 仅作为真实对象归纳前提消费。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaFiberUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaOutputSyntax SyntaxMixedFormulaJudgmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_unique {m} {Γ : Context m} (w r s a b c d n q v : Fin m)
    (hu : Derives Γ (uniqueOutput w r s a b c d n v)) (hq : Derives Γ (substituted w r s a b c d n q)) :
    Derives Γ (.equal q v) := by
  have hh := Derives.allE q hu
  have hp : Derives Γ ((substituted w r s a b c d n q).imp (.equal q v)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh
  exact .impE hp hq

theorem fiber_unique {m} {Γ : Context m} (w r s a b c d n q v : Fin m)
    (hf : Derives Γ (fiber w r s a b c d n)) (hq : Derives Γ (substituted w r s a b c d n q))
    (hv : Derives Γ (substituted w r s a b c d n v)) : Derives Γ (.equal q v) := by
  let B := (substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
    (uniqueOutput w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hf
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hq1 : Derives Δ (substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (substituted_rename w r s a b c d n q Fin.castSucc) (under hq B)
  have hv1 : Derives Δ (substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc v.castSucc) := of_eq (substituted_rename w r s a b c d n v Fin.castSucc) (under hv B)
  exact eq_trans (at_unique _ _ _ _ _ _ _ _ _ _ (.conjR hB) hq1) (eq_symm (at_unique _ _ _ _ _ _ _ _ _ _ (.conjR hB) hv1))

theorem property_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (property w n))
    (hq : Derives Γ (substituted w r s a b c d n q)) (hv : Derives Γ (substituted w r s a b c d n v)) : Derives Γ (.equal q v) := by
  have hi := SyntaxMixedFormulaOutput.input_of_substituted hZ w r s a b c d n q hw hq
  have hf := Derives.impE (property_at w n r s a b c d hp) hi
  exact fiber_unique w r s a b c d n q v hf hq hv
end PPAC.Migration.Internal.SyntaxMixedFormulaFiberUnique
