import PPAC.Migration.Internal.ProjectBoundShiftPoint

/-! All candidate outputs of the internal bound shift: uniqueness, range, exact scope. -/
namespace PPAC.Migration.Internal.ProjectBoundShiftLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectBoundShiftSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y q : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (shifted w x y)) (hq : Derives Γ (shifted w x q)) : Derives Γ (.equal y q) := by
  let B := body w x y
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hy
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hq2 := of_eq (shifted_rename w x q (old 2)) (HornBinderRules.under_body 2 hq B)
  let C := body (old 2 w) (old 2 x) (old 2 q)
  let Ξ := Context.add C (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 C _ hq2
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hw4 := of_eq (omega_rename (old 2 w) (old 2)) (HornBinderRules.under_body 2 hw2 C)
  have hB4 := of_eq (matrix_rename (old 2 w) (old 2 x) (old 2 y) (slot 2 0) (slot 2 1) (old 2)) (HornBinderRules.under_body 2 hB C)
  exact ProjectBoundShiftPoint.matrix_unique (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 hZ B) C)
    (old 2 (old 2 w)) (old 2 (old 2 x)) (old 2 (old 2 y)) (old 2 (old 2 q))
    (old 2 (slot 2 0)) (old 2 (slot 2 1)) (slot 2 0) (slot 2 1) hw4 hB4 hC

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shifted w x y)) : Derives Γ (.mem y w) := by
  let B := body w x y
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hs
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  exact SyntaxVariableDecode.range (HornBinderRules.zf_body 2 hZ B) true (old 2 w) (slot 2 1) (old 2 y) hw2 (.conjR (.conjR hB))

theorem target_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B f x y : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w))
    (hB : Derives Γ (successor B b)) (hx : Derives Γ (SyntaxTermSyntax.branch true w b x))
    (hs : Derives Γ (shifted w x y)) : Derives Γ (SyntaxTermSyntax.term w B f y) := by
  let K := body w x y
  let Δ := Context.add K (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 K _ hs
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw K)
  have hb2 : Derives Δ (.mem (old 2 b) (old 2 w)) := HornBinderRules.under_body 2 hb K
  have hf2 : Derives Δ (.mem (old 2 f) (old 2 w)) := HornBinderRules.under_body 2 hf K
  have hB2 := of_eq (successor_rename B b (old 2)) (HornBinderRules.under_body 2 hB K)
  have hx2 := of_eq (SyntaxTermSyntax.branch_rename true w b x (old 2)) (HornBinderRules.under_body 2 hx K)
  have ho := ProjectBoundShiftPoint.matrix_type (HornBinderRules.zf_body 2 hZ K) (old 2 w) (old 2 b) (old 2 B) (old 2 f)
    (old 2 x) (old 2 y) (slot 2 0) (slot 2 1) hw2 hb2 hf2 hB2 hx2 hK
  exact of_eq (SyntaxTermSyntax.term_rename w B f y (old 2)).symm ho

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (shifted w x y)) : Derives Γ (uniqueOutput w x y) := by
  apply Derives.allI
  apply Derives.impI
  let E := shifted w.castSucc x.castSucc (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hy1 := of_eq (shifted_rename w x y Fin.castSucc) (under hy E)
  exact unique (ZFContext.under hZ E) w.castSucc x.castSucc (Fin.last m) y.castSucc hw1 (.hyp (Or.inl rfl)) hy1

end PPAC.Migration.Internal.ProjectBoundShiftLaws
