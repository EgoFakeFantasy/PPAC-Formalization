import PPAC.Migration.Internal.OriginalArgumentFieldSyntax

/-! 原Cons的全部内部索引逐字段对应：真实零／后继分解，尾字段不借宿主索引。 -/
namespace PPAC.Migration.Internal.OriginalArgumentConsFields
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax OriginalArgumentFieldSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter ell k h t H T n q i x y : Fin m)
    (hw : Derives Γ (omega w))
    (hh : Derives Γ (Formula.mem h w))
    (ht : Derives Γ (Formula.mem t w))
    (hH : Derives Γ (Formula.mem H w))
    (hT : Derives Γ (Formula.mem T w))
    (hell : Derives Γ (Formula.mem ell w))
    (hs : Derives Γ (successor k ell))
    (hci : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hco : Derives Γ (StructuralListSyntax.consCode w H T q))
    (hhead : Derives Γ (OriginalTransformRowSyntax.run 1 w mode depth parameter h H))
    (htail : Derives Γ (OriginalArgumentFieldSyntax.fields w mode depth parameter ell t T))
    (hi : Derives Γ (Formula.mem i k))
    (hx : Derives Γ (StructuralListFieldSyntax.field w n i x))
    (hy : Derives Γ (StructuralListFieldSyntax.field w q i y))
    : Derives Γ (OriginalTransformRowSyntax.run 1 w mode depth parameter x y) := by
  have hk := OmegaStructureAlgebra.successor_member w k ell (ZFContext.arithmetic hZ).base.extensionality hw hell hs
  have hiN := StructuralListTraceOrder.member_member hZ w i k hw hk hi
  have hc := OmegaStructureAlgebra.decomposition_at w i (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hiN
  apply Derives.disjE hc
  · let E := empty i
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hX := StructuralListFieldCons.zero_point (ZFContext.add hZ E) w h t n i x (add hw E) (add hh E) (add ht E) (add hci E) hE (add hx E)
    have hY := StructuralListFieldCons.zero_point (ZFContext.add hZ E) w H T q i y (add hw E) (add hH E) (add hT E) (add hco E) hE (add hy E)
    exact OriginalRunValueSubstitution.run_output 1 w mode depth parameter x H y (eq_symm hY)
      (OriginalRunValueSubstitution.run_input 1 w mode depth parameter h H x (eq_symm hX) (add hhead E))
  · let E := OmegaStructureSyntax.predecessor w i
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (under (add hw E) B)
    have hh1 : Derives Δ (Formula.mem h.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under (add hh E) B)
    have ht1 : Derives Δ (Formula.mem t.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under (add ht E) B)
    have hH1 : Derives Δ (Formula.mem H.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under (add hH E) B)
    have hT1 : Derives Δ (Formula.mem T.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under (add hT E) B)
    have hell1 : Derives Δ (Formula.mem ell.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under (add hell E) B)
    have hs1 : Derives Δ (successor k.castSucc ell.castSucc) := of_eq (by simp only [successor_rename]) (under (add hs E) B)
    have hci1 : Derives Δ (StructuralListSyntax.consCode w.castSucc h.castSucc t.castSucc n.castSucc) := of_eq (by simp only [StructuralListSyntax.consCode_rename]) (under (add hci E) B)
    have hco1 : Derives Δ (StructuralListSyntax.consCode w.castSucc H.castSucc T.castSucc q.castSucc) := of_eq (by simp only [StructuralListSyntax.consCode_rename]) (under (add hco E) B)
    have htail1 : Derives Δ (OriginalArgumentFieldSyntax.fields w.castSucc mode.castSucc depth.castSucc parameter.castSucc ell.castSucc t.castSucc T.castSucc) := of_eq (by simp only [OriginalArgumentFieldSyntax.fields_rename]) (under (add htail E) B)
    have hi1 : Derives Δ (Formula.mem i.castSucc k.castSucc) := of_eq (by simp only [Formula.rename]) (under (add hi E) B)
    have hx1 : Derives Δ (StructuralListFieldSyntax.field w.castSucc n.castSucc i.castSucc x.castSucc) := of_eq (by simp only [StructuralListFieldSyntax.field_rename]) (under (add hx E) B)
    have hy1 : Derives Δ (StructuralListFieldSyntax.field w.castSucc q.castSucc i.castSucc y.castSucc) := of_eq (by simp only [StructuralListFieldSyntax.field_rename]) (under (add hy E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hj := SyntaxIndexLiftOrder.predecessor_member hZ1 w.castSucc ell.castSucc k.castSucc i.castSucc (Fin.last m) hw1 hell1 hs1 hi1 (.conjR hB)
    have hfx := StructuralListFieldCons.successor_forward hZ1 w.castSucc h.castSucc t.castSucc n.castSucc (Fin.last m) i.castSucc x.castSucc hw1 hh1 ht1 (.conjL hB) (.conjR hB) hci1 hx1
    have hfy := StructuralListFieldCons.successor_forward hZ1 w.castSucc H.castSucc T.castSucc q.castSucc (Fin.last m) i.castSucc y.castSucc hw1 hH1 hT1 (.conjL hB) (.conjR hB) hco1 hy1
    have ho := fields_at w.castSucc mode.castSucc depth.castSucc parameter.castSucc ell.castSucc t.castSucc T.castSucc (Fin.last m) x.castSucc y.castSucc htail1 hj hfx hfy
    exact of_eq (OriginalTransformRowSyntax.run_rename 1 w mode depth parameter x y Fin.castSucc).symm ho

theorem cons_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter ell k h t H T n q : Fin m)
    (hw : Derives Γ (omega w))
    (hh : Derives Γ (Formula.mem h w))
    (ht : Derives Γ (Formula.mem t w))
    (hH : Derives Γ (Formula.mem H w))
    (hT : Derives Γ (Formula.mem T w))
    (hell : Derives Γ (Formula.mem ell w))
    (hs : Derives Γ (successor k ell))
    (hci : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hco : Derives Γ (StructuralListSyntax.consCode w H T q))
    (hhead : Derives Γ (OriginalTransformRowSyntax.run 1 w mode depth parameter h H))
    (htail : Derives Γ (OriginalArgumentFieldSyntax.fields w mode depth parameter ell t T))
    : Derives Γ (fields w mode depth parameter k n q) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (Formula.mem (slot 3 0) (old 3 k)).conj ((StructuralListFieldSyntax.field (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).conj (StructuralListFieldSyntax.field (old 3 w) (old 3 q) (slot 3 0) (slot 3 2)))
  let Δ := Context.add A (raisedContext 3 Γ)
  have hZ3 := HornBinderRules.zf_body 3 hZ A
  have hw3 : Derives Δ (omega (old 3 w)) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 3 hw A)
  have hh3 : Derives Δ (Formula.mem (old 3 h) (old 3 w)) := of_eq (by simp only [Formula.rename]) (HornBinderRules.under_body 3 hh A)
  have ht3 : Derives Δ (Formula.mem (old 3 t) (old 3 w)) := of_eq (by simp only [Formula.rename]) (HornBinderRules.under_body 3 ht A)
  have hH3 : Derives Δ (Formula.mem (old 3 H) (old 3 w)) := of_eq (by simp only [Formula.rename]) (HornBinderRules.under_body 3 hH A)
  have hT3 : Derives Δ (Formula.mem (old 3 T) (old 3 w)) := of_eq (by simp only [Formula.rename]) (HornBinderRules.under_body 3 hT A)
  have hell3 : Derives Δ (Formula.mem (old 3 ell) (old 3 w)) := of_eq (by simp only [Formula.rename]) (HornBinderRules.under_body 3 hell A)
  have hs3 : Derives Δ (successor (old 3 k) (old 3 ell)) := of_eq (by simp only [successor_rename]) (HornBinderRules.under_body 3 hs A)
  have hci3 : Derives Δ (StructuralListSyntax.consCode (old 3 w) (old 3 h) (old 3 t) (old 3 n)) := of_eq (by simp only [StructuralListSyntax.consCode_rename]) (HornBinderRules.under_body 3 hci A)
  have hco3 : Derives Δ (StructuralListSyntax.consCode (old 3 w) (old 3 H) (old 3 T) (old 3 q)) := of_eq (by simp only [StructuralListSyntax.consCode_rename]) (HornBinderRules.under_body 3 hco A)
  have hhead3 : Derives Δ (OriginalTransformRowSyntax.run 1 (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 h) (old 3 H)) := of_eq (by simp only [OriginalTransformRowSyntax.run_rename]) (HornBinderRules.under_body 3 hhead A)
  have htail3 : Derives Δ (OriginalArgumentFieldSyntax.fields (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 ell) (old 3 t) (old 3 T)) := of_eq (by simp only [OriginalArgumentFieldSyntax.fields_rename]) (HornBinderRules.under_body 3 htail A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  exact at_index hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 ell) (old 3 k) (old 3 h) (old 3 t) (old 3 H) (old 3 T) (old 3 n) (old 3 q) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hh3 ht3 hH3 hT3 hell3 hs3 hci3 hco3 hhead3 htail3 (.conjL hA) (.conjL (.conjR hA)) (.conjR (.conjR hA))

end PPAC.Migration.Internal.OriginalArgumentConsFields
