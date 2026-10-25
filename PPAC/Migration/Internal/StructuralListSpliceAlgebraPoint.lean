import PPAC.Migration.Internal.StructuralListSpliceAlgebraCons

/-! Nil and actual Cons prove the joint algebra property from the genuine smaller-prefix property. -/
namespace PPAC.Migration.Internal.StructuralListSpliceAlgebraPoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListSpliceSyntax StructuralListSpliceAlgebraSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem nil_right {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n e : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n))
    (he : Derives Γ (StructuralListSyntax.nilCode w e)) : Derives Γ (splice w n e n) := by
  have heq := StructuralNil.unique hZ w e n hw he hn
  have hv := StructuralListTraceBase.valid_nil hZ w e hw he
  exact .impE (.conjR (StructuralListSplice.nil_iff hZ _ _ _ _ hw hn)) (.conjI hv heq)

theorem nil_associate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n B C AB BC O : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n))
    (hAB : Derives Γ (splice w n B AB)) (hBC : Derives Γ (splice w B C BC)) :
    Derives Γ ((splice w AB C O).iff (splice w n BC O)) := by
  have hEq := Derives.conjR (.impE (.conjL (StructuralListSplice.nil_iff hZ w n B AB hw hn)) hAB)
  apply Derives.conjI
  · apply Derives.impI
    let H := splice w AB C O
    have hBCO := StructuralListSpliceAlgebraTransport.prefix_subst w AB C O B (eq_symm (add hEq H)) (.hyp (Or.inl rfl))
    have heq := StructuralListSpliceTotal.unique (ZFContext.add hZ H) _ _ _ _ _ (add hw H) hBCO (add hBC H)
    have hv := StructuralListSplice.joined_valid _ _ _ _ (add hBC H)
    exact .impE (.conjR (StructuralListSplice.nil_iff (ZFContext.add hZ H) _ _ _ _ (add hw H) (add hn H))) (.conjI hv (eq_symm heq))
  · apply Derives.impI
    let H := splice w n BC O
    have heq := Derives.conjR (.impE (.conjL (StructuralListSplice.nil_iff (ZFContext.add hZ H) w n BC O (add hw H) (add hn H))) (.hyp (Or.inl rfl)))
    have hBCO := StructuralListSpliceAlgebraTransport.output w B C BC O heq (add hBC H)
    exact StructuralListSpliceAlgebraTransport.prefix_subst w B C O AB (add hEq H) hBCO

theorem cons_right {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n e : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) (hi : Derives Γ (rightNil w x))
    (he : Derives Γ (StructuralListSyntax.nilCode w e)) : Derives Γ (splice w n e n) := by
  have hSmall := right_at w x e hi he
  have hRem := StructuralListSplice.intro_remaining w h x e n x hSmall hc
  exact StructuralListSplice.cons_backward hZ _ _ _ _ _ _ hw hh hc hRem

theorem nil_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) : Derives Γ (property w n) := by
  apply Derives.impI
  let N := StructuralListTraceSyntax.valid w n
  apply Derives.conjI
  · apply Derives.allI
    apply Derives.impI
    let E := StructuralListSyntax.nilCode w.castSucc (Fin.last m)
    have hZ1 := ZFContext.under (ZFContext.add hZ N) E
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw N) E)
    have hn1 := of_eq (StructuralListSyntax.nilCode_rename w n Fin.castSucc) (under (add hn N) E)
    exact nil_right hZ1 _ _ _ hw1 hn1 (.hyp (Or.inl rfl))
  · apply OriginalUniversalBlock.intro_many 5 (associativeBody w n)
    apply Derives.impI
    apply Derives.impI
    let A := splice (old 5 w) (old 5 n) (slot 5 0) (slot 5 2)
    let B := splice (old 5 w) (slot 5 0) (slot 5 1) (slot 5 3)
    let Δ := Context.add B (Context.add A (raisedContext 5 (Context.add N Γ)))
    have hZ5 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 5 (ZFContext.add hZ N)) A) B
    have hw5 := of_eq (omega_rename w (old 5)) (add (add (HornBinderRules.under_many 5 (add hw N)) A) B)
    have hn5 := of_eq (StructuralListSyntax.nilCode_rename w n (old 5)) (add (add (HornBinderRules.under_many 5 (add hn N)) A) B)
    exact nil_associate hZ5 (old 5 w) (old 5 n) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) hw5 hn5 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem cons_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) (hi : Derives Γ (property w x)) : Derives Γ (property w n) := by
  apply Derives.impI
  let N := StructuralListTraceSyntax.valid w n
  have hV : Derives (Context.add N Γ) N := .hyp (Or.inl rfl)
  have hXV := StructuralListDecode.tail_valid (ZFContext.add hZ N) _ _ _ _ (add hw N) (add hh N) (add hx N) (add hc N) hV
  have hInfo := Derives.impE (add hi N) hXV
  apply Derives.conjI
  · apply Derives.allI
    apply Derives.impI
    let E := StructuralListSyntax.nilCode w.castSucc (Fin.last m)
    have hZ1 := ZFContext.under (ZFContext.add hZ N) E
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw N) E)
    have hh1 : Derives (Context.add E (Context.image Formula.raise (Context.add N Γ))) (.mem h.castSucc w.castSucc) := under (add hh N) E
    have hc1 := of_eq (StructuralListSyntax.consCode_rename w h x n Fin.castSucc) (under (add hc N) E)
    have hr1 := of_eq (rightNil_rename w x Fin.castSucc) (under (.conjL hInfo) E)
    exact cons_right hZ1 _ _ _ _ _ hw1 hh1 hc1 hr1 (.hyp (Or.inl rfl))
  · apply OriginalUniversalBlock.intro_many 5 (associativeBody w n)
    apply Derives.impI
    apply Derives.impI
    let A := splice (old 5 w) (old 5 n) (slot 5 0) (slot 5 2)
    let B := splice (old 5 w) (slot 5 0) (slot 5 1) (slot 5 3)
    let Δ := Context.add B (Context.add A (raisedContext 5 (Context.add N Γ)))
    have hZ5 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 5 (ZFContext.add hZ N)) A) B
    have lift {φ : Formula m} (hp : Derives Γ φ) : Derives Δ (φ.rename (old 5)) := add (add (HornBinderRules.under_many 5 (add hp N)) A) B
    have hw5 := of_eq (omega_rename w (old 5)) (lift hw)
    have hh5 : Derives Δ (.mem (old 5 h) (old 5 w)) := lift hh
    have hx5 : Derives Δ (.mem (old 5 x) (old 5 w)) := lift hx
    have hc5 := of_eq (StructuralListSyntax.consCode_rename w h x n (old 5)) (lift hc)
    have ha5 := of_eq (associative_rename w x (old 5)) (add (add (HornBinderRules.under_many 5 (.conjR hInfo)) A) B)
    exact StructuralListSpliceAlgebraCons.associate hZ5 (old 5 w) (old 5 h) (old 5 x) (old 5 n) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) hw5 hh5 hx5 hc5 ha5 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.StructuralListSpliceAlgebraPoint
