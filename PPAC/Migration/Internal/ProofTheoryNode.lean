import PPAC.Migration.Internal.ProofTheoryNodeSyntax

/-! 原节点完整对象双条件，无合法前驱／类型／搜索界额外前提。 -/
namespace PPAC.Migration.Internal.ProofTheoryNode
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open ProofTheoryNodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem matrix_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix test w row env).iff (normalizedMatrix test w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix test w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjL (ProofTheoryQueries.head_iff (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR (.conjR hE)))
    have hq := Derives.impE (.conjL (ProofTheoryQueries.bundle_iff test (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR (.conjR hE)))
    exact .conjI hn (.conjI hh hq)
  · apply Derives.impI
    let E := normalizedMatrix test w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjR (ProofTheoryQueries.head_iff (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR hE))
    have hb := ProofTheoryQueries.all_assignment_bounds (ZFContext.add hZ E) w row env (add hw E) hn hh
    have hq := Derives.impE (.conjR (ProofTheoryQueries.bundle_iff test (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    exact .conjI hn (.conjI hb (.conjI hh hq))

theorem normalized_node_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node test w row).iff (normalized test w z row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  have hwN := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  have hzN := of_eq (empty_rename z (old 3)) (HornBinderRules.under_many 3 hz)
  exact matrix_iff test (HornBinderRules.zf_many 3 hZ) (old 3 w) (old 3 z) (old 3 row) (slot 3) hwN hzN

end PPAC.Migration.Internal.ProofTheoryNode
