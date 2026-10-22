import PPAC.Migration.Internal.SyntaxRenameOperatorRows

/-! 重命名状态集合的全候选成员精确式；实际同码状态恢复全部元数据，排除非自然源与杂项。 -/
namespace PPAC.Migration.Internal.SyntaxRenameOperatorMembership
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameLocalSyntax SyntaxRenameOperatorSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem no_junk {m} {Γ : Context m} (w n h v p : Fin m)
    (hv : Derives Γ (value w n h v)) (hp : Derives Γ (.mem p v)) :
    Derives Γ ((Formula.mem p w).conj (row w n h p)) := .impE (.conjL (value_at w n h v p hv)) hp

theorem member_recognized {m} {Γ : Context m} (w n h v p : Fin m)
    (hv : Derives Γ (value w n h v)) (hp : Derives Γ (.mem p v)) :
    Derives Γ (SyntaxRenameStateSyntax.recognized w p) :=
  SyntaxRenameOperatorRows.recognized w n h p (.conjR (no_junk w n h v p hv hp))

theorem source_natural {m} {Γ : Context m} (w n h v p : Fin m)
    (hv : Derives Γ (value w n h v)) (hp : Derives Γ (.mem p v)) : Derives Γ (.mem n w) :=
  SyntaxRenameOperatorRows.source_natural w n h p (.conjR (no_junk w n h v p hv hp))

theorem at_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h v p R S a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w n h v))
    (hp : Derives Γ (SyntaxRenameStateSyntax.state w R S a b c d q p)) :
    Derives Γ ((Formula.mem p v).iff (content w R S a b c d h n q)) := by
  have hr := SyntaxRenameOperatorRows.state_iff hZ w n h p R S a b c d q hw hp
  have hn := SyntaxRenameState.natural hZ w R S a b c d q p hw (.conjL hp)
  have he := value_at w n h v p hv
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hr) _) (.conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact .impE (add (.conjR he) _) (.conjI (add hn _) (.impE (add (.conjR hr) _) (.hyp (Or.inl rfl))))

theorem off_natural {m} {Γ : Context m} (w n h v : Fin m)
    (hn : Derives Γ (Formula.mem n w).neg) (hv : Derives Γ (value w n h v)) : Derives Γ (empty v) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) v.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 := of_eq (value_rename w n h v Fin.castSucc) (under hv M)
  exact .impE (under hn M) (source_natural _ _ _ _ _ hv1 (.hyp (Or.inl rfl)))
end PPAC.Migration.Internal.SyntaxRenameOperatorMembership
