import PPAC.Migration.Internal.SyntaxForallClosureTypingSyntax

/-! Arithmetic reindexing and exact quantified-code typing for the closure induction. -/
namespace PPAC.Migration.Internal.SyntaxForallClosureTypingHelpers
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_sum {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b source : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hb : Derives Γ (.mem b w))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w z b source)) : Derives Γ (.equal source b) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hc := ZFArithmetic.add_commute hZ w z b source hw hzW hb hs
  exact NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (NaturalAdditionSyntax.params w) w b z source hz hc

theorem move_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s b c source : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hb : Derives Γ (.mem b w))
    (hs : Derives Γ (successor s n)) (hc : Derives Γ (successor c b))
    (ht : Derives Γ (NaturalAdditionSyntax.sum w s b source)) : Derives Γ (NaturalAdditionSyntax.sum w n c source) := by
  have hsW := OmegaStructureAlgebra.successor_member w s n (ZFContext.arithmetic hZ).base.extensionality hw hn hs
  have hbs := ZFArithmetic.add_commute hZ w s b source hw hsW hb ht
  have he := ZFArithmetic.add_exists hZ w b n hw hb hn
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (NaturalAdditionSyntax.sum w.castSucc b.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hs1 := of_eq (successor_rename s n Fin.castSucc) (under hs E)
  have hc1 := of_eq (successor_rename c b Fin.castSucc) (under hc E)
  have hbs1 := of_eq (NaturalAdditionSyntax.sum_rename w b s source Fin.castSucc) (under hbs E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hv := ZFArithmetic.add_succ_forward hZ1 w.castSucc b.castSucc n.castSucc s.castSucc (Fin.last m) source.castSucc
    hw1 (under hb E) (under hn E) hs1 (.conjR hE) hbs1
  have hnb := ZFArithmetic.add_commute hZ1 w.castSucc b.castSucc n.castSucc (Fin.last m) hw1 (under hb E) (under hn E) (.conjR hE)
  exact of_eq (by simp only [Formula.raise, NaturalAdditionSyntax.sum_rename])
    (ZFArithmetic.add_succ_backward hZ1 w.castSucc n.castSucc b.castSucc c.castSucc (Fin.last m) source.castSucc
      hw1 (under hn E) (under hb E) hc1 hnb hv)

theorem quantified_at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b c f x y : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w))
    (hc : Derives Γ (successor c b))
    (hy : Derives Γ (SyntaxNodeSyntax.constructor 1 9 w (fun _ => x) y)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w y b f).iff (FormulaCodeSyntax.formulaCode w x c f)) := by
  have h0 := FormulaCodeKnownLogical.forall_iff hZ w b f x y hw hy
  have h1 := FormulaCodeBranchSyntax.at_successor hZ w x b f c hc
  apply Derives.conjI
  · apply Derives.impI
    have ha := Derives.conjR (Derives.impE (add (.conjL h0) _) (.hyp (Or.inl rfl)))
    exact .impE (add (.conjL h1) _) ha
  · apply Derives.impI
    have ha := Derives.impE (add (.conjR h1) _) (.hyp (Or.inl rfl))
    exact .impE (add (.conjR h0) _) (.conjI (.conjI (add hb _) (add hf _)) ha)

end PPAC.Migration.Internal.SyntaxForallClosureTypingHelpers
