import PPAC.Migration.Internal.MemberPairAgreement

/-! 独立参数程序的两个真实输出与原App，合成为纯成员程序候选输出。 -/
namespace PPAC.Migration.Internal.MemberProgramOutput
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S c d s x y q zero args : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 zero))
    (ho : Derives Γ (OriginalFormulaApplicationSyntax.application w zero args q))
    (hp : Derives Γ (ArgumentPairProgramSyntax.returned w R S c d x y args)) :
    Derives Γ (MemberProgramSyntax.returned w R S c d s x y q) := by
  let B := ArgumentPairProgramSyntax.body w R S c d x y args
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hp
  have hZ1 := HornBinderRules.zf_body 2 hZ B
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 2)) := HornBinderRules.under_body 2 h B
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (lift hw)
  have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar (old 2 w) (old 2 s)) := of_eq (SyntaxAtomSyntax.zeroScalar_rename w s (old 2)) (lift hs)
  have hz1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (old 2 zero)) := of_eq (SyntaxNumeralSyntax.numeral_rename 0 zero (old 2)) (lift hz)
  have ho1 : Derives Δ (OriginalFormulaApplicationSyntax.application (old 2 w) (old 2 zero) (old 2 args) (old 2 q)) := of_eq (OriginalFormulaApplicationSyntax.application_rename w zero args q (old 2)) (lift ho)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hMember := Derives.impE (.conjL (OriginalFormulaMemberApplication.member_at_forest_iff hZ1 (old 2 w) (old 2 zero) (old 2 s) (slot 2 0) (slot 2 1) (old 2 args) (old 2 q) hw1 hz1 hs1 (.conjL (.conjR hB)))) ho1
  have hOut := MemberProgramSyntax.intro_returned _ _ _ _ _ _ _ _ _ _ _ (.conjL hB) hMember (.conjR (.conjR hB))
  exact of_eq (MemberProgramSyntax.returned_rename w R S c d s x y q (old 2)).symm hOut

end PPAC.Migration.Internal.MemberProgramOutput
