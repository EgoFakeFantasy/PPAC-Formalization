import PPAC.Migration.Internal.ProofSubstitutionNodeSyntax

/-! 原替换模式完整有界节点与语法／替换程序／前驱字段规格对象等价，搜索界已实际消去。 -/
namespace PPAC.Migration.Internal.ProofSubstitutionNode
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax ProofSubstitutionNodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix w row env).iff (specificationMatrix w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hm := Derives.conjR (.conjR hE)
    have hs := Derives.impE (.conjL (ProofSubstitutionAllQueries.bundle_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR hm)
    exact .conjI hn (.conjI (.conjL hm) hs)
  · apply Derives.impI
    let E := specificationMatrix w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.conjL (.conjR hE)
    have hb := Derives.impE (.conjR (ProofSubstitutionAllQueries.bundle_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    have hformula := Derives.conjL (.conjR (.conjR (.conjR hb)))
    have hbound := ProofSubstitutionBounds.environment_bound (ZFContext.add hZ E) w row env (add hw E) hn hh hformula
    exact .conjI hn (.conjI hbound (.conjI hh hb))

theorem node_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node w row).iff (specification w z row)) := by
  apply HornApplicationBounds.existsMany_congr 6
  have hw6 := of_eq (omega_rename w (old 6)) (HornBinderRules.under_many 6 hw)
  have hz6 := of_eq (empty_rename z (old 6)) (HornBinderRules.under_many 6 hz)
  exact matrix_iff (HornBinderRules.zf_many 6 hZ) (old 6 w) (old 6 z) (old 6 row) (slot 6) hw6 hz6

end PPAC.Migration.Internal.ProofSubstitutionNode
