import PPAC.Migration.Internal.StructuralListSpliceAlgebraInduction

/-! Right-Nil identity, exact singleton splice and all-candidate associativity hold for actual internal lists after all prefix IH are discharged. -/
namespace PPAC.Migration.Internal.StructuralListSpliceAlgebra
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSpliceSyntax StructuralListSpliceAlgebraSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem right_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n e : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListTraceSyntax.valid w n))
    (he : Derives Γ (StructuralListSyntax.nilCode w e)) : Derives Γ (splice w n e n) := by
  have hp := StructuralListSpliceAlgebraInduction.at_code hZ w n hw (StructuralListValidity.range w n hn)
  exact right_at w n e (.conjL (.impE hp hn)) he

theorem right_nil_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n e a : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (StructuralListSyntax.nilCode w e)) :
    Derives Γ ((splice w n e a).iff ((StructuralListTraceSyntax.valid w n).conj (.equal a n))) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := splice w n e a
    have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have hN := StructuralListSplice.prefix_valid _ _ _ _ hH
    have hIdentity := right_nil (ZFContext.add hZ H) w n e (add hw H) hN (add he H)
    exact .conjI hN (StructuralListSpliceTotal.unique (ZFContext.add hZ H) _ _ _ _ _ (add hw H) hH hIdentity)
  · apply Derives.impI
    let H := (StructuralListTraceSyntax.valid w n).conj (.equal a n)
    have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have hIdentity := right_nil (ZFContext.add hZ H) w n e (add hw H) (.conjL hH) (add he H)
    exact StructuralListSpliceAlgebraTransport.output w n e n a (eq_symm (.conjR hH)) hIdentity

theorem associative_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w A B C AB BC O : Fin m)
    (hw : Derives Γ (omega w)) (hAB : Derives Γ (splice w A B AB)) (hBC : Derives Γ (splice w B C BC)) :
    Derives Γ ((splice w AB C O).iff (splice w A BC O)) := by
  have hA := StructuralListSplice.prefix_valid _ _ _ _ hAB
  have hProp := StructuralListSpliceAlgebraInduction.at_code hZ w A hw (StructuralListValidity.range w A hA)
  have hAssoc := Derives.conjR (.impE hProp hA)
  exact associate_at w A B C AB BC O hAssoc hAB hBC

theorem associate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w A B C AB BC O : Fin m)
    (hw : Derives Γ (omega w)) (hAB : Derives Γ (splice w A B AB)) (hBC : Derives Γ (splice w B C BC))
    (hO : Derives Γ (splice w AB C O)) : Derives Γ (splice w A BC O) :=
  .impE (.conjL (associative_iff hZ w A B C AB BC O hw hAB hBC)) hO

theorem associate_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w A B C AB BC O : Fin m)
    (hw : Derives Γ (omega w)) (hAB : Derives Γ (splice w A B AB)) (hBC : Derives Γ (splice w B C BC))
    (hO : Derives Γ (splice w A BC O)) : Derives Γ (splice w AB C O) :=
  .impE (.conjR (associative_iff hZ w A B C AB BC O hw hAB hBC)) hO

theorem singleton_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h e S T O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w))
    (he : Derives Γ (StructuralListSyntax.nilCode w e)) (hS : Derives Γ (StructuralListSyntax.consCode w h e S))
    (hT : Derives Γ (StructuralListTraceSyntax.valid w T)) :
    Derives Γ ((splice w S T O).iff (StructuralListSyntax.consCode w h T O)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := splice w S T O
    let R := (splice w.castSucc e.castSucc T.castSucc (Fin.last m)).conj (StructuralListSyntax.consCode w.castSucc h.castSucc (Fin.last m) O.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    have hEN := StructuralNil.range hZ w e hw he
    apply Derives.exE (p := R) (StructuralListSplice.cons_forward (ZFContext.add hZ H) w h e S T O (add hw H) (add hh H) (add hEN H) (add hS H) (.hyp (Or.inl rfl)))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have he1 := of_eq (StructuralListSyntax.nilCode_rename w e Fin.castSucc) (under (add he H) R)
    have hEq := Derives.conjR (.impE (.conjL (StructuralListSplice.nil_iff hZ1 w.castSucc e.castSucc T.castSucc (Fin.last m) hw1 he1)) (.conjL hR))
    simpa only [Formula.raise,StructuralListSyntax.consCode_rename] using StructuralListSpliceTotalSyntax.cons_tail _ _ _ _ _ (eq_symm hEq) (.conjR hR)
  · apply Derives.impI
    let H := StructuralListSyntax.consCode w h T O
    have hSmall := Derives.impE (.conjR (StructuralListSplice.nil_iff (ZFContext.add hZ H) w e T T (add hw H) (add he H))) (.conjI (add hT H) (.eqRefl T))
    have hRem := StructuralListSplice.intro_remaining w h e T O T hSmall (.hyp (Or.inl rfl))
    exact StructuralListSplice.cons_backward (ZFContext.add hZ H) w h e S T O (add hw H) (add hh H) (add hS H) hRem

theorem snoc_cons_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w A e h S AH T HT O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w))
    (he : Derives Γ (StructuralListSyntax.nilCode w e)) (hS : Derives Γ (StructuralListSyntax.consCode w h e S))
    (hAH : Derives Γ (splice w A S AH)) (hT : Derives Γ (StructuralListTraceSyntax.valid w T))
    (hHT : Derives Γ (StructuralListSyntax.consCode w h T HT)) :
    Derives Γ ((splice w AH T O).iff (splice w A HT O)) := by
  have hST := Derives.impE (.conjR (singleton_iff hZ w h e S T HT hw hh he hS hT)) hHT
  exact associative_iff hZ w A S T AH HT O hw hAH hST

end PPAC.Migration.Internal.StructuralListSpliceAlgebra
