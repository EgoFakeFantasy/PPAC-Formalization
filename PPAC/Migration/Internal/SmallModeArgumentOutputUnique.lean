import PPAC.Migration.Internal.SmallModeArgumentsRun
import PPAC.Migration.Internal.OriginalArgumentValueSyntax

/-! 对原Run₂全部内部候选的Nil／Cons输出唯一性；真实子运行提供组件自然性。 -/
namespace PPAC.Migration.Internal.SmallModeArgumentOutputUnique
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_case_against_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (StructuralListSyntax.nilCode w n))
    (hc : Derives Γ (OriginalArgumentCaseSyntax.consCase w mode depth parameter n q)) : Derives Γ .bot := by
  let C := OriginalArgumentCaseSyntax.consBody w mode depth parameter n q
  let Δ := Context.add C (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 C _ hc
  have hw4 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw C)
  have hn4 : Derives Δ (StructuralListSyntax.nilCode (old 4 w) (old 4 n)) := of_eq (StructuralListSyntax.nilCode_rename w n (old 4)) (HornBinderRules.under_body 4 hn C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact StructuralConsUnique.disjoint (HornBinderRules.zf_body 4 hZ C) (old 4 w) (slot 4 0) (slot 4 1) (old 4 n) hw4 hn4 (.conjL (.conjL hC))

theorem nil_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter n q v : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (StructuralListSyntax.nilCode w n)) (hq : Derives Γ (StructuralListSyntax.nilCode w q))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 2 w mode depth parameter n v)) : Derives Γ (.equal v q) := by
  have he := Derives.impE (.conjL (SmallModeArgumentsRun.run_iff hZ modeIndex hSmall w mode depth parameter n v hw hm hd hp)) hr
  apply Derives.disjE he
  · let E := OriginalArgumentCaseSyntax.nilData w n v
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact StructuralNil.unique (ZFContext.add hZ E) w v q (add hw E) (.conjR hE) (add hq E)
  · let E := OriginalArgumentCaseSyntax.consCase w mode depth parameter n v
    exact .botE (cons_case_against_nil (ZFContext.add hZ E) w mode depth parameter n v (add hw E) (add hn E) (.hyp (Or.inl rfl)))

theorem cons_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter ell c d n q h t H T v : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hci : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hco : Derives Γ (StructuralListSyntax.consCode w H T q))
    (hh : Derives Γ (OriginalNumericTermValueSyntax.value w mode depth parameter c d h H))
    (ht : Derives Γ (OriginalArgumentValueSyntax.value w mode depth parameter ell c d t T))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 2 w mode depth parameter n v)) : Derives Γ (.equal v q) := by
  have he := Derives.impE (.conjL (SmallModeArgumentsRun.run_iff hZ modeIndex hSmall w mode depth parameter n v hw hm hd hp)) hr
  apply Derives.disjE he
  · let E := OriginalArgumentCaseSyntax.nilData w n v
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact .botE (StructuralConsUnique.disjoint (ZFContext.add hZ E) w h t n (add hw E) (.conjL hE) (add hci E))
  · let E := OriginalArgumentCaseSyntax.consCase w mode depth parameter n v
    let C := OriginalArgumentCaseSyntax.consBody w mode depth parameter n v
    let Δ := Context.add C (raisedContext 4 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 4 C _ (.hyp (Or.inl rfl))
    have hZ4 := HornBinderRules.zf_body 4 (ZFContext.add hZ E) C
    have hw4 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 (add hw E) C)
    have hci4 : Derives Δ (StructuralListSyntax.consCode (old 4 w) (old 4 h) (old 4 t) (old 4 n)) := of_eq (StructuralListSyntax.consCode_rename w h t n (old 4)) (HornBinderRules.under_body 4 (add hci E) C)
    have hco4 : Derives Δ (StructuralListSyntax.consCode (old 4 w) (old 4 H) (old 4 T) (old 4 q)) := of_eq (StructuralListSyntax.consCode_rename w H T q (old 4)) (HornBinderRules.under_body 4 (add hco E) C)
    have hh4 : Derives Δ (OriginalNumericTermValueSyntax.value (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 c) (old 4 d) (old 4 h) (old 4 H)) := of_eq (OriginalNumericTermValueSyntax.value_rename w mode depth parameter c d h H (old 4)) (HornBinderRules.under_body 4 (add hh E) C)
    have ht4 : Derives Δ (OriginalArgumentValueSyntax.value (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 ell) (old 4 c) (old 4 d) (old 4 t) (old 4 T)) := of_eq (OriginalArgumentValueSyntax.value_rename w mode depth parameter ell c d t T (old 4)) (HornBinderRules.under_body 4 (add ht E) C)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hHead := Derives.conjL (Derives.conjR hC)
    have hTail := Derives.conjR (Derives.conjR hC)
    have hhN := OriginalArgumentRunNaturality.input_natural hZ4 1 _ _ _ _ _ _ hw4 (.conjL hh4)
    have htN := OriginalArgumentRunNaturality.input_natural hZ4 2 _ _ _ _ _ _ hw4 (.conjL ht4)
    have hhN' := OriginalArgumentRunNaturality.input_natural hZ4 1 _ _ _ _ _ _ hw4 hHead
    have htN' := OriginalArgumentRunNaturality.input_natural hZ4 2 _ _ _ _ _ _ hw4 hTail
    have hi := StructuralConsUnique.injective hZ4 (old 4 w) (old 4 h) (old 4 t) (slot 4 0) (slot 4 1) (old 4 n) hw4 hhN htN hhN' htN' hci4 (.conjL (.conjL hC))
    have hHeadAligned := OriginalRunValueSubstitution.run_input 1 (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (slot 4 0) (slot 4 2) (old 4 h) (eq_symm (.conjL hi)) hHead
    have hTailAligned := OriginalRunValueSubstitution.run_input 2 (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (slot 4 1) (slot 4 3) (old 4 t) (eq_symm (.conjR hi)) hTail
    have hH := OriginalNumericTermValueSyntax.unique (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 c) (old 4 d) (old 4 h) (old 4 H) (slot 4 2) hh4 hHeadAligned
    have hT := OriginalArgumentValueSyntax.unique (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 ell) (old 4 c) (old 4 d) (old 4 t) (old 4 T) (slot 4 3) ht4 hTailAligned
    have hOutput := OriginalRunValueSubstitution.cons_tail (old 4 w) (old 4 H) (slot 4 3) (old 4 v) (old 4 T) hT
      (OriginalRunValueSubstitution.cons_head (old 4 w) (slot 4 2) (slot 4 3) (old 4 v) (old 4 H) hH (.conjR (.conjL hC)))
    have hHN := OriginalNumericTermValueSyntax.output_natural _ _ _ _ _ _ _ _ hh4
    have hTN := OriginalArgumentValueSyntax.output_natural _ _ _ _ _ _ _ _ _ ht4
    exact eq_symm (StructuralConsUnique.unique hZ4 (old 4 w) (old 4 H) (old 4 T) (old 4 q) (old 4 v) hw4 hHN hTN hco4 hOutput)

end PPAC.Migration.Internal.SmallModeArgumentOutputUnique
