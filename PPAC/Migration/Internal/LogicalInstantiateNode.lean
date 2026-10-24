import PPAC.Migration.Internal.LogicalInstantiateNodeSyntax

/-! 三个原逻辑模式的完整节点双条件；实际查询、全部赋值界及嵌套数值头均对象证明。 -/
namespace PPAC.Migration.Internal.LogicalInstantiateNode
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax LogicalInstantiateNodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem matrix4_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w z row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix4 universal w row env).iff (specificationMatrix4 universal w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix4 universal w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hm := Derives.conjR (.conjR hE)
    have hs := Derives.impE (.conjL (LogicalInstantiateAllQueries.bundle4_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR hm)
    exact .conjI hn (.conjI (.conjL hm) hs)
  · apply Derives.impI
    let E := specificationMatrix4 universal w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.conjL (.conjR hE)
    have hb := Derives.impE (.conjR (LogicalInstantiateAllQueries.bundle4_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    have hbound := head4_bounds (ZFContext.add hZ E) universal w row env (add hw E) hn hh
    exact .conjI hn (.conjI hbound (.conjI hh hb))

theorem node4_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node4 universal w row).iff (specification4 universal w z row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  have hwN := of_eq (omega_rename w (old 4)) (HornBinderRules.under_many 4 hw)
  have hzN := of_eq (empty_rename z (old 4)) (HornBinderRules.under_many 4 hz)
  exact matrix4_iff (HornBinderRules.zf_many 4 hZ) universal (old 4 w) (old 4 z) (old 4 row) (slot 4) hwN hzN

theorem specification4_normalized_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w z row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((specificationMatrix4 universal w z row env).iff (normalizedMatrix4 universal w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := specificationMatrix4 universal w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjL (head4_normalized_iff (ZFContext.add hZ E) universal w row env (add hw E) hn)) (.conjL (.conjR hE))
    exact .conjI hn (.conjI hh (.conjR (.conjR hE)))
  · apply Derives.impI
    let E := normalizedMatrix4 universal w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjR (head4_normalized_iff (ZFContext.add hZ E) universal w row env (add hw E) hn)) (.conjL (.conjR hE))
    exact .conjI hn (.conjI hh (.conjR (.conjR hE)))

theorem normalized_node4_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node4 universal w row).iff (normalized4 universal w z row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  have hwN := of_eq (omega_rename w (old 4)) (HornBinderRules.under_many 4 hw)
  have hzN := of_eq (empty_rename z (old 4)) (HornBinderRules.under_many 4 hz)
  exact SyntaxTypeLocalTransfer.iff_trans (matrix4_iff (HornBinderRules.zf_many 4 hZ) universal (old 4 w) (old 4 z) (old 4 row) (slot 4) hwN hzN)
    (specification4_normalized_iff (HornBinderRules.zf_many 4 hZ) universal (old 4 w) (old 4 z) (old 4 row) (slot 4) hwN)

theorem matrix6_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix6 w row env).iff (specificationMatrix6 w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix6 w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hm := Derives.conjR (.conjR hE)
    have hs := Derives.impE (.conjL (LogicalInstantiateAllQueries.bundle6_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR hm)
    exact .conjI hn (.conjI (.conjL hm) hs)
  · apply Derives.impI
    let E := specificationMatrix6 w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.conjL (.conjR hE)
    have hb := Derives.impE (.conjR (LogicalInstantiateAllQueries.bundle6_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    have hbound := head6_bounds (ZFContext.add hZ E) w row env (add hw E) hn hh
    exact .conjI hn (.conjI hbound (.conjI hh hb))

theorem node6_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node6 w row).iff (specification6 w z row)) := by
  apply HornApplicationBounds.existsMany_congr 6
  have hwN := of_eq (omega_rename w (old 6)) (HornBinderRules.under_many 6 hw)
  have hzN := of_eq (empty_rename z (old 6)) (HornBinderRules.under_many 6 hz)
  exact matrix6_iff (HornBinderRules.zf_many 6 hZ) (old 6 w) (old 6 z) (old 6 row) (slot 6) hwN hzN

theorem specification6_normalized_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((specificationMatrix6 w z row env).iff (normalizedMatrix6 w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := specificationMatrix6 w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjL (head6_normalized_iff (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR hE))
    exact .conjI hn (.conjI hh (.conjR (.conjR hE)))
  · apply Derives.impI
    let E := normalizedMatrix6 w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjR (head6_normalized_iff (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR hE))
    exact .conjI hn (.conjI hh (.conjR (.conjR hE)))

theorem normalized_node6_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node6 w row).iff (normalized6 w z row)) := by
  apply HornApplicationBounds.existsMany_congr 6
  have hwN := of_eq (omega_rename w (old 6)) (HornBinderRules.under_many 6 hw)
  have hzN := of_eq (empty_rename z (old 6)) (HornBinderRules.under_many 6 hz)
  exact SyntaxTypeLocalTransfer.iff_trans (matrix6_iff (HornBinderRules.zf_many 6 hZ) (old 6 w) (old 6 z) (old 6 row) (slot 6) hwN hzN)
    (specification6_normalized_iff (HornBinderRules.zf_many 6 hZ) (old 6 w) (old 6 z) (old 6 row) (slot 6) hwN)

end PPAC.Migration.Internal.LogicalInstantiateNode
