import PPAC.Migration.Internal.ProjectSubsetPoint

/-! Subset expansion graph: all internal candidates, unique output, exact original type. -/
namespace PPAC.Migration.Internal.ProjectSubsetLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectSubsetSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z x y q r : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (expanded w b z x y q))
    (hr : Derives Γ (expanded w b z x y r)) : Derives Γ (.equal q r) := by
  let B := body w b z x y q
  let Δ := Context.add B (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 hw B)
  have hr8 := of_eq (expanded_rename w b z x y r (old 8)) (HornBinderRules.under_body 8 hr B)
  let C := body (old 8 w) (old 8 b) (old 8 z) (old 8 x) (old 8 y) (old 8 r)
  let Ξ := Context.add C (raisedContext 8 Δ)
  apply HornBinderRules.eliminate_many 8 C _ hr8
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hw16 := of_eq (omega_rename (old 8 w) (old 8)) (HornBinderRules.under_body 8 hw8 C)
  have hB16 := of_eq (matrix_rename (old 8 w) (old 8 b) (old 8 z) (old 8 x) (old 8 y) (old 8 q) (slot 8) (old 8)) (HornBinderRules.under_body 8 hB C)
  exact ProjectSubsetPoint.matrix_unique (HornBinderRules.zf_body 8 (HornBinderRules.zf_body 8 hZ B) C)
    (old 8 (old 8 w)) (old 8 (old 8 b)) (old 8 (old 8 z)) (old 8 (old 8 x)) (old 8 (old 8 y))
    (old 8 (old 8 q)) (old 8 (old 8 r)) (fun i => old 8 (slot 8 i)) (slot 8) hw16 hB16 hC

theorem target_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z x y q : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hx : Derives Γ (SyntaxTermSyntax.branch true w b x)) (hy : Derives Γ (SyntaxTermSyntax.branch true w b y))
    (he : Derives Γ (expanded w b z x y q)) : Derives Γ (FormulaCodeSyntax.formulaCode w q b z) := by
  let K := body w b z x y q
  let Δ := Context.add K (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 K _ he
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 hw K)
  have hb8 : Derives Δ (.mem (old 8 b) (old 8 w)) := HornBinderRules.under_body 8 hb K
  have hz8 := of_eq (empty_rename z (old 8)) (HornBinderRules.under_body 8 hz K)
  have hx8 := of_eq (SyntaxTermSyntax.branch_rename true w b x (old 8)) (HornBinderRules.under_body 8 hx K)
  have hy8 := of_eq (SyntaxTermSyntax.branch_rename true w b y (old 8)) (HornBinderRules.under_body 8 hy K)
  have ho := ProjectSubsetPoint.matrix_type (HornBinderRules.zf_body 8 hZ K) (old 8 w) (old 8 b) (old 8 z) (old 8 x) (old 8 y) (old 8 q)
    (slot 8) hw8 hb8 hz8 hx8 hy8 hK
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w q b z (old 8)).symm ho

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z x y q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (expanded w b z x y q)) : Derives Γ (.mem q w) := by
  let K := body w b z x y q
  let Δ := Context.add K (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 K _ he
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 hw K)
  exact SyntaxNodeInjective.constructor_range (HornBinderRules.zf_body 8 hZ K) 1 9 (old 8 w) (fun _ => slot 8 7) (old 8 q) hw8
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hK))))))))

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z x y q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (expanded w b z x y q)) : Derives Γ (uniqueOutput w b z x y q) := by
  apply Derives.allI
  apply Derives.impI
  let E := expanded w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hq1 := of_eq (expanded_rename w b z x y q Fin.castSucc) (under hq E)
  exact unique (ZFContext.under hZ E) w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) hq1

end PPAC.Migration.Internal.ProjectSubsetLaws
