import PPAC.Migration.Internal.ProofLogicalNodeSyntax

/-! 原节点完整对象双条件，无合法前驱／类型／搜索界额外前提。 -/
namespace PPAC.Migration.Internal.ProofLogicalNode
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open ProofLogicalNodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix w row env).iff (normalizedMatrix w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjL (ProofLogicalQueries.head_iff (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR (.conjR hE)))
    have hq := Derives.impE (.conjL (ProofLogicalQueries.query_normalized_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR (.conjR hE)))
    exact .conjI hn (.conjI hh hq)
  · apply Derives.impI
    let E := normalizedMatrix w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjR (ProofLogicalQueries.head_iff (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR hE))
    have hb := ProofLogicalQueries.all_assignment_bounds (ZFContext.add hZ E) w row env (add hw E) hn hh
    have hq := Derives.impE (.conjR (ProofLogicalQueries.query_normalized_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    exact .conjI hn (.conjI hb (.conjI hh hq))

theorem normalized_node_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node w row).iff (normalized w z row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  have hwN := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  have hzN := of_eq (empty_rename z (old 3)) (HornBinderRules.under_many 3 hz)
  exact matrix_iff (HornBinderRules.zf_many 3 hZ) (old 3 w) (old 3 z) (old 3 row) (slot 3) hwN hzN

end PPAC.Migration.Internal.ProofLogicalNode
