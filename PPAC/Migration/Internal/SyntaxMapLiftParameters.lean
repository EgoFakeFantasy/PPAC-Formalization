import PPAC.Migration.Internal.ObjectSyntaxRenameRecursive

/-! 原自然映射码提升的真实后继恢复与所有候选后继/输出码参数唯一性。 -/
namespace PPAC.Migration.Internal.SyntaxMapLiftParameters
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxMapLiftSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem successors {m} {Γ : Context m} (w a c k u v l : Fin m)
    (hl : Derives Γ (codedLift w a c k u v l)) : Derives Γ ((successor u a).conj (successor v c)) := by
  let B := SyntaxMapLiftSyntax.body w a c k u v l
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_lift w a c k u v l _ hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hL := Derives.conjL (.conjR hB)
  have ho := Derives.conjI (.conjL (.conjR hL)) (.conjL (.conjR (.conjR hL)))
  exact of_eq (by simp only [Formula.raise, Formula.rename, successor_rename]) ho

theorem subst_u {m} {Γ : Context m} (w a c k u v l u1 : Fin m)
    (he : Derives Γ (.equal u u1)) (hl : Derives Γ (codedLift w a c k u v l)) :
    Derives Γ (codedLift w a c k u1 v l) := by
  let P := codedLift w.castSucc a.castSucc c.castSucc k.castSucc (Fin.last m) v.castSucc l.castSucc
  have e0 : P.instantiate u = codedLift w a c k u v l := by
    simp only [P, Formula.instantiate, codedLift_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate u1 = codedLift w a c k u1 v l := by
    simp only [P, Formula.instantiate, codedLift_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem subst_v {m} {Γ : Context m} (w a c k u v l v1 : Fin m)
    (he : Derives Γ (.equal v v1)) (hl : Derives Γ (codedLift w a c k u v l)) :
    Derives Γ (codedLift w a c k u v1 l) := by
  let P := codedLift w.castSucc a.castSucc c.castSucc k.castSucc u.castSucc (Fin.last m) l.castSucc
  have e0 : P.instantiate v = codedLift w a c k u v l := by
    simp only [P, Formula.instantiate, codedLift_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate v1 = codedLift w a c k u v1 l := by
    simp only [P, Formula.instantiate, codedLift_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c k u v l U V L : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (codedLift w a c k u v l))
    (hL : Derives Γ (codedLift w a c k U V L)) :
    Derives Γ ((Formula.equal u U).conj ((Formula.equal v V).conj (.equal l L))) := by
  have hs := successors w a c k u v l hl
  have hS := successors w a c k U V L hL
  have hu := InsertLogic.unique u U a a (ZFContext.arithmetic hZ).base.extensionality (.conjL hs) (.conjL hS)
  have hv := InsertLogic.unique v V c c (ZFContext.arithmetic hZ).base.extensionality (.conjR hs) (.conjR hS)
  have hp := subst_v w a c k U v l V hv (subst_u w a c k u v l U hu hl)
  have he := SyntaxMapLiftFiber.unique hZ w a c k U V l L hw hp hL
  exact .conjI hu (.conjI hv he)
end PPAC.Migration.Internal.SyntaxMapLiftParameters
