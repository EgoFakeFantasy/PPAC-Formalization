import PPAC.Migration.Internal.AbstractVariableSpecialization
import PPAC.Migration.Internal.SyntaxIndexLiftOrder

/-! 任意内部深度的移位分支及后继阈值律；没有原运行或环境一致性前提。 -/
namespace PPAC.Migration.Internal.AbstractBoundOrder
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem above_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i j x y : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w))
    (hj : Derives Γ (successor j i)) (hdi : Derives Γ (.mem d j)) :
    Derives Γ ((boundValue w d i x y).iff (SyntaxVariableSyntax.code true w j y)) := by
  have hle := NaturalOrderBasic.member_successor d i j hj hdi
  apply Derives.conjI
  · apply Derives.impI
    let E := boundValue w d i x y
    apply Derives.disjE (.hyp (Γ := Context.add E Γ) (Or.inl rfl))
    · exact .botE (NaturalOrderBasic.below_not_reverse (ZFContext.add (ZFContext.add hZ E) _) w d i
        (add (add hw E) _) (add (add hd E) _) (add (add hle E) _) (.conjL (.hyp (Or.inl rfl))))
    · let F := boundShifted w d i y
      let B := (successor (Fin.last m) i.castSucc).conj ((Formula.mem d.castSucc (Fin.last m)).conj
        (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) y.castSucc))
      let Δ := Context.add B (Context.image Formula.raise (Context.add F (Context.add E Γ)))
      apply Derives.exE (p := B) (.hyp (Or.inl rfl))
      have hj1 := of_eq (successor_rename j i Fin.castSucc) (under (add (add hj E) F) B)
      have hB : Derives Δ B := .hyp (Or.inl rfl)
      have he := OmegaUniversal.successor_unique (Fin.last m) j.castSucc i.castSucc
        (ZFContext.arithmetic (ZFContext.under (ZFContext.add (ZFContext.add hZ E) F) B)).base.extensionality (.conjL hB) hj1
      have ho := AbstractVariableIndex.code_index_subst true _ _ _ _ he (.conjR (.conjR hB))
      exact of_eq (SyntaxVariableSyntax.code_rename true w j y Fin.castSucc).symm ho
  · exact .impI (.disjR (intro_boundShifted w d i y j (add hj _) (add hdi _) (.hyp (Or.inl rfl))))

theorem successor_threshold_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i D I : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (hi : Derives Γ (.mem i w))
    (hD : Derives Γ (successor D d)) (hI : Derives Γ (successor I i)) :
    Derives Γ ((Formula.mem I D).iff (.mem i d)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact SyntaxIndexLiftOrder.predecessor_member (ZFContext.add hZ _) w d D I i
      (add hw _) (add hd _) (add hD _) (.hyp (Or.inl rfl)) (add hI _)
  · apply Derives.impI
    exact SyntaxIndexLiftOrder.successor_member (ZFContext.add hZ _) w i d I D
      (add hw _) (add hi _) (add hd _) (.hyp (Or.inl rfl)) (add hI _) (add hD _)

theorem above_successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i D I J x y : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (hi : Derives Γ (.mem i w))
    (hD : Derives Γ (successor D d)) (hI : Derives Γ (successor I i))
    (hJ : Derives Γ (successor J I)) (hdi : Derives Γ (.mem d I)) :
    Derives Γ ((boundValue w D I x y).iff (SyntaxVariableSyntax.code true w J y)) := by
  have hIn := OmegaStructureAlgebra.successor_member w I i (ZFContext.arithmetic hZ).base.extensionality hw hi hI
  have hDn := OmegaStructureAlgebra.successor_member w D d (ZFContext.arithmetic hZ).base.extensionality hw hd hD
  have hDI := SyntaxIndexLiftOrder.successor_member hZ w d I D J hw hd hIn hdi hD hJ
  exact above_iff hZ w D I J x y hw hDn hJ hDI

end PPAC.Migration.Internal.AbstractBoundOrder
