import PPAC.Migration.Internal.ProofStrengtheningNodeSyntax

/-! 原strengthening模式完整有界节点与公式／完整mode0程序／前驱字段规格对象等价，搜索界已实际消去。 -/
namespace PPAC.Migration.Internal.ProofStrengtheningNode
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax ProofStrengtheningNodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix w row env).iff (specificationMatrix w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hm := Derives.conjR (.conjR hE)
    have hs := Derives.impE (.conjL (ProofStrengtheningAllQueries.bundle_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR hm)
    exact .conjI hn (.conjI (.conjL hm) hs)
  · apply Derives.impI
    let E := specificationMatrix w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.conjL (.conjR hE)
    have hb := Derives.impE (.conjR (ProofStrengtheningAllQueries.bundle_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    have hpredecessorFormula := Derives.conjL (.conjR (.conjR hb))
    have hbound := ProofStrengtheningBounds.environment_bound (ZFContext.add hZ E) w row env (add hw E) hn hh hpredecessorFormula
    exact .conjI hn (.conjI hbound (.conjI hh hb))

theorem node_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node w row).iff (specification w z row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  have hw6 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_many 4 hw)
  have hz6 := of_eq (empty_rename z (old 4)) (HornBinderRules.under_many 4 hz)
  exact matrix_iff (HornBinderRules.zf_many 4 hZ) (old 4 w) (old 4 z) (old 4 row) (slot 4) hw6 hz6

end PPAC.Migration.Internal.ProofStrengtheningNode
