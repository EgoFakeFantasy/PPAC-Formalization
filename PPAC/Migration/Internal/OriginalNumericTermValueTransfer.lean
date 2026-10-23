import PPAC.Migration.Internal.OriginalNumericTermValueSyntax

/-! 实际程序值纤维经已证全候选双条件传到原Run₁；不抽取宿主输出。 -/
namespace PPAC.Migration.Internal.OriginalNumericTermValueTransfer
open Source SourceAlgebra SourceLogic OriginalNumericTermValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem value_of_program {m} {Γ : Context m} (w mode depth parameter R S a b c d n q : Fin m)
    (ha : Derives Γ (agreement w mode depth parameter R S n))
    (hv : Derives Γ (TermTransformProgramValueSyntax.value w R S a b c d n q)) :
    Derives Γ (value w mode depth parameter c d n q) := by
  have hr := Derives.impE (.conjR (OriginalNumericTermValueSyntax.agreement_at w mode depth parameter R S n q ha)) (.conjR (.conjL hv))
  apply Derives.conjI hr
  apply Derives.conjI (.conjL (.conjR hv))
  apply Derives.conjI (.conjL (.conjR (.conjR hv)))
  apply Derives.allI
  apply Derives.impI
  let E := OriginalTransformRowSyntax.run 1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have ha1 : Derives Δ (agreement w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc n.castSucc) := of_eq (agreement_rename w mode depth parameter R S n Fin.castSucc) (under ha E)
  have hv1 : Derives Δ (TermTransformProgramValueSyntax.value w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (TermTransformProgramValueSyntax.value_rename w R S a b c d n q Fin.castSucc) (under hv E)
  have hp := Derives.impE (.conjL (OriginalNumericTermValueSyntax.agreement_at _ _ _ _ _ _ _ (Fin.last m) ha1)) (.hyp (Or.inl rfl))
  have hc : Derives Δ (TermTransformProgramSyntax.checked w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := .conjI (.conjL (.conjL hv1)) hp
  have hu := Derives.allE (Fin.last m) (.conjR (.conjR (.conjR hv1)))
  have hu1 : Derives Δ ((TermTransformProgramSyntax.checked w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, TermTransformProgramSyntax.checked_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hu
  exact .impE hu1 hc

theorem fiber_of_program {m} {Γ : Context m} (w mode depth parameter R S a b c d n : Fin m)
    (ha : Derives Γ (agreement w mode depth parameter R S n))
    (hf : Derives Γ (TermTransformProgramValueSyntax.fiber w R S a b c d n)) :
    Derives Γ (fiber w mode depth parameter c d n) := by
  let V := TermTransformProgramValueSyntax.value w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) hf
  have ha1 : Derives Δ (agreement w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc n.castSucc) := of_eq (agreement_rename w mode depth parameter R S n Fin.castSucc) (under ha V)
  have hv := value_of_program w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) ha1 (.hyp (Or.inl rfl))
  exact of_eq (fiber_rename w mode depth parameter c d n Fin.castSucc).symm
    (intro_fiber _ _ _ _ _ _ _ _ hv)

end PPAC.Migration.Internal.OriginalNumericTermValueTransfer
