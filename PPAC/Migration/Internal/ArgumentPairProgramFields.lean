import PPAC.Migration.Internal.ArgumentPairProgramSyntax

/-! 原全内部字段像在真实两个输入参数处，等价于内部存在的有类型双输出程序运行。 -/
namespace PPAC.Migration.Internal.ArgumentPairProgramFields
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ArgumentForestProgramSyntax ArgumentPairProgramSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem mapped_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S len c d n q x y : Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (SyntaxNumeralSyntax.numeral 2 len))
    (hn : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n)) :
    Derives Γ ((ArgumentProgramFieldSyntax.mapped w R S len c d n q).iff (returned w R S c d x y q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := ArgumentProgramFieldSyntax.mapped w R S len c d n q
    let B := ArgumentPairOutput.body w c d q
    let Δ := Context.add B (raisedContext 2 (Context.add E Γ))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have he := ArgumentPairOutput.exists_output (ZFContext.add hZ E) w len c d q (add hw E) (add hl E) (.conjL hE)
    apply HornBinderRules.eliminate_many 2 B _ he
    have hZ1 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) B
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 2)) := HornBinderRules.under_body 2 (add h E) B
    have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (lift hw)
    have hl1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 (old 2 len)) := of_eq (SyntaxNumeralSyntax.numeral_rename 2 len (old 2)) (lift hl)
    have hn1 : Derives Δ (SyntaxForestSyntax.forest 2 (old 2 w) (SyntaxAtomSyntax.two (old 2 x) (old 2 y)) (old 2 n)) := of_eq (by simp only [SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (lift hn)
    have hf1 : Derives Δ (ArgumentProgramFieldSyntax.fields (old 2 w) (old 2 R) (old 2 S) (old 2 len) (old 2 n) (old 2 q)) := of_eq (ArgumentProgramFieldSyntax.fields_rename w R S len n q (old 2)) (HornBinderRules.under_body 2 (.conjR hE) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hr := ArgumentForestProgramFields.runs_of_fields hZ1 2 (old 2 w) (old 2 R) (old 2 S) (old 2 len) (old 2 n) (old 2 q) (SyntaxAtomSyntax.two (old 2 x) (old 2 y)) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1)) hw1 hl1 hn1 (.conjR hB) hf1
    have hOut := intro_returned _ _ _ _ _ _ _ _ _ _ (.conjL hB) (.conjR hB) hr
    exact of_eq (returned_rename w R S c d x y q (old 2)).symm hOut
  · apply Derives.impI
    let E := returned w R S c d x y q
    let B := body w R S c d x y q
    let Δ := Context.add B (raisedContext 2 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 2 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) B
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 2)) := HornBinderRules.under_body 2 (add h E) B
    have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (lift hw)
    have hl1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 (old 2 len)) := of_eq (SyntaxNumeralSyntax.numeral_rename 2 len (old 2)) (lift hl)
    have hn1 : Derives Δ (SyntaxForestSyntax.forest 2 (old 2 w) (SyntaxAtomSyntax.two (old 2 x) (old 2 y)) (old 2 n)) := of_eq (by simp only [SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (lift hn)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hc := Derives.conjL (Derives.conjL (Derives.conjL hB))
    have he := ArgumentForestProgramFields.mapped_iff hZ1 2 (old 2 w) (old 2 R) (old 2 S) (old 2 len) (old 2 c) (old 2 d) (old 2 n) (old 2 q) (SyntaxAtomSyntax.two (old 2 x) (old 2 y)) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1)) hw1 hl1 hc hn1 (.conjL (.conjR hB))
    have hMapped := Derives.impE (.conjR he) (.conjI (.conjL hB) (.conjR (.conjR hB)))
    exact of_eq (ArgumentProgramFieldSyntax.mapped_rename w R S len c d n q (old 2)).symm hMapped

end PPAC.Migration.Internal.ArgumentPairProgramFields
