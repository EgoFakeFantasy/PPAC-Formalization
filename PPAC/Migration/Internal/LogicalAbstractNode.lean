import PPAC.Migration.Internal.LogicalAbstractNodeSyntax

/-! 原21／24全部赋值界及数值完整节点双条件；对象前提仅Ω与empty。 -/
namespace PPAC.Migration.Internal.LogicalAbstractNode
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax LogicalAbstractNodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem head21_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hh : Derives Γ (graph head21 w env row)) : Derives Γ (HornExprBounds.environmentBound 5 row env) :=
  HornExprBounds.intro_environmentBound row env (fun i => HornExprBounds.variable_bound hZ head21 i (head21_variables i) w row env hw hn hh)

theorem matrix21_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix21 w row env).iff (normalizedMatrix21 w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix21 w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.conjL (.conjR (.conjR hE))
    have ht := Derives.impE (.conjL (LogicalAbstractAllQueries.bundle21_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR (.conjR hE)))
    have hc := Derives.impE (.conjL (LogicalRule21Head.head_iff (ZFContext.add hZ E) w row env (add hw E) hn)) hh
    exact .conjI hn (.conjI hc ht)
  · apply Derives.impI
    let E := normalizedMatrix21 w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjR (LogicalRule21Head.head_iff (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR hE))
    have hb := head21_bounds (ZFContext.add hZ E) w row env (add hw E) hn hh
    have hq := Derives.impE (.conjR (LogicalAbstractAllQueries.bundle21_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    exact .conjI hn (.conjI hb (.conjI hh hq))

theorem normalized_node21_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node21 w row).iff (normalized21 w z row)) := by
  apply HornApplicationBounds.existsMany_congr 5
  have hwN := of_eq (omega_rename w (old 5)) (HornBinderRules.under_many 5 hw)
  have hzN := of_eq (empty_rename z (old 5)) (HornBinderRules.under_many 5 hz)
  exact matrix21_iff (HornBinderRules.zf_many 5 hZ) (old 5 w) (old 5 z) (old 5 row) (slot 5) hwN hzN

theorem head24_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hh : Derives Γ (graph head24 w env row)) : Derives Γ (HornExprBounds.environmentBound 4 row env) :=
  HornExprBounds.intro_environmentBound row env (fun i => HornExprBounds.variable_bound hZ head24 i (head24_variables i) w row env hw hn hh)

theorem matrix24_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix24 w row env).iff (normalizedMatrix24 w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix24 w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.conjL (.conjR (.conjR hE))
    have ht := Derives.impE (.conjL (LogicalAbstractAllQueries.bundle24_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR (.conjR hE)))
    have hc := Derives.impE (.conjL (LogicalRule24Head.head_iff (ZFContext.add hZ E) w row env (add hw E) hn)) hh
    exact .conjI hn (.conjI hc ht)
  · apply Derives.impI
    let E := normalizedMatrix24 w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjR (LogicalRule24Head.head_iff (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR hE))
    have hb := head24_bounds (ZFContext.add hZ E) w row env (add hw E) hn hh
    have hq := Derives.impE (.conjR (LogicalAbstractAllQueries.bundle24_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    exact .conjI hn (.conjI hb (.conjI hh hq))

theorem normalized_node24_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node24 w row).iff (normalized24 w z row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  have hwN := of_eq (omega_rename w (old 4)) (HornBinderRules.under_many 4 hw)
  have hzN := of_eq (empty_rename z (old 4)) (HornBinderRules.under_many 4 hz)
  exact matrix24_iff (HornBinderRules.zf_many 4 hZ) (old 4 w) (old 4 z) (old 4 row) (slot 4) hwN hzN

end PPAC.Migration.Internal.LogicalAbstractNode
