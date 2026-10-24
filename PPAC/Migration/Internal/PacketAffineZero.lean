import PPAC.Migration.Internal.PacketAffineCore

/-! Exact zero-tail behavior of the real affine cell, including invalid output candidates. -/
namespace PPAC.Migration.Internal.PacketAffineZero
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineSyntax PacketAffineCore ZFArithmetic
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem equation_zero {m} {Γ : Context m} (w B d z n : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (equation w B d z n)) : Derives Γ (.equal n d) := by
  let P := equationBody w B d z n
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz P)
  have hp0 := NaturalMultiplicationLaws.zero_forward w.castSucc B.castSucc z.castSucc (Fin.last m) hz1 (.conjL hP)
  exact NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (NaturalAdditionSyntax.params w.castSucc)
    w.castSucc d.castSucc (Fin.last m) n.castSucc hp0 (.conjR hP)

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d z n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((affine w B d z n).iff ((Formula.mem d B).conj (.equal n d))) := by
  apply Derives.conjI
  · apply Derives.impI
    let A := affine w B d z n
    have hA : Derives (Context.add A Γ) A := .hyp (Or.inl rfl)
    exact .conjI (digit_guard w B d z n hA) (equation_zero w B d z n (add hz A) (equation_of_affine w B d z n hA))
  · apply Derives.impI
    let A := (Formula.mem d B).conj (.equal n d)
    let Δ := Context.add A Γ
    have hA : Derives Δ A := .hyp (Or.inl rfl)
    have hZE := ZFContext.add hZ A
    have hwE := add hw A
    have hBE := add hB A
    have hzE := add hz A
    have hdN := StructuralListTraceOrder.member_member hZE w d B hwE hBE (.conjL hA)
    have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZE).base.extensionality hwE hzE
    have hnN := mem_subst (eq_symm (.conjR hA)) hdN
    have hp := mul_zero hZE w B z z hwE hBE hzE hzE
    have hs := NaturalAdditionSyntax.output_subst w d z d n (eq_symm (.conjR hA)) (add_zero hZE w d z hwE hdN hzE)
    exact intro_affine w B d z n z hBE (.conjL hA) hzN hnN hp hs

end PPAC.Migration.Internal.PacketAffineZero
