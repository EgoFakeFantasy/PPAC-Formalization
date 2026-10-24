import PPAC.Migration.Internal.ProofMPNodeSyntax

/-! 原MP模式完整有界节点与公式／蕴含码／前驱字段规格对象等价，搜索界已实际消去。 -/
namespace PPAC.Migration.Internal.ProofMPNode
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax ProofMPNodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix w row env).iff (specificationMatrix w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hm := Derives.conjR (.conjR hE)
    have hs := Derives.impE (.conjL (ProofMPAllQueries.bundle_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR hm)
    exact .conjI hn (.conjI (.conjL hm) hs)
  · apply Derives.impI
    let E := specificationMatrix w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.conjL (.conjR hE)
    have hb := Derives.impE (.conjR (ProofMPAllQueries.bundle_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    have hleftFormula := Derives.conjL (.conjR (.conjR (.conjR hb)))
    have hbound := ProofMPBounds.environment_bound (ZFContext.add hZ E) w row env (add hw E) hn hh hleftFormula
    exact .conjI hn (.conjI hbound (.conjI hh hb))

theorem node_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node w row).iff (specification w z row)) := by
  apply HornApplicationBounds.existsMany_congr 5
  have hw6 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_many 5 hw)
  have hz6 := of_eq (empty_rename z (old 5)) (HornBinderRules.under_many 5 hz)
  exact matrix_iff (HornBinderRules.zf_many 5 hZ) (old 5 w) (old 5 z) (old 5 row) (slot 5) hw6 hz6

end PPAC.Migration.Internal.ProofMPNode
