import PPAC.Migration.Internal.AbstractVariableRun
import PPAC.Migration.Internal.GodelUnpairArithmetic
import PPAC.Migration.Internal.StructuralNodeCore

/-! 原mode1数值关系的零深度／零索引／后继与深度内分支消去；全为内部自然顺序推导。 -/
namespace PPAC.Migration.Internal.AbstractVariableSpecialization
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem successor_not_empty {m} {Γ : Context m} (i k : Fin m) (hs : Derives Γ (successor i k))
    (hz : Derives Γ (empty i)) : Derives Γ .bot :=
  .impE (empty_at i k hz) (InsertLogic.new_member i k k hs)

theorem bound_zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z i j x y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (.mem i w))
    (hj : Derives Γ (successor j i)) :
    Derives Γ ((boundValue w z i x y).iff (SyntaxVariableSyntax.code true w j y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundValue w z i x y
    apply Derives.disjE (.hyp (Γ := Context.add E Γ) (Or.inl rfl))
    · exact .botE (.impE (add (add (empty_at z i hz) E) _) (.conjL (.hyp (Or.inl rfl))))
    · let F := boundShifted w z i y
      let B := (successor (Fin.last m) i.castSucc).conj ((Formula.mem z.castSucc (Fin.last m)).conj
        (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) y.castSucc))
      let Δ := Context.add B (Context.image Formula.raise (Context.add F (Context.add E Γ)))
      apply Derives.exE (p := B) (.hyp (Or.inl rfl))
      have hj1 := of_eq (successor_rename j i Fin.castSucc) (under (add (add hj E) F) B)
      have hB : Derives Δ B := .hyp (Or.inl rfl)
      have he := OmegaUniversal.successor_unique (Fin.last m) j.castSucc i.castSucc
        (ZFContext.arithmetic (ZFContext.under (ZFContext.add (ZFContext.add hZ E) F) B)).base.extensionality (.conjL hB) hj1
      have ho := AbstractVariableIndex.code_index_subst true _ _ _ _ he (.conjR (.conjR hB))
      exact of_eq (SyntaxVariableSyntax.code_rename true w j y Fin.castSucc).symm ho
  · apply Derives.impI
    let E := SyntaxVariableSyntax.code true w j y
    have hzj := NaturalOrderBasic.below_successor z i j (add hj E)
      (GodelUnpairArithmetic.zero_below (ZFContext.add hZ E) w z i (add hw E) (add hz E) (add hi E))
    exact .disjR (intro_boundShifted w z i y j (add hj E) hzj (.hyp (Or.inl rfl)))

theorem free_zero_iff {m} {Γ : Context m} (w d i y : Fin m) (hi : Derives Γ (empty i)) :
    Derives Γ ((freeValue w d i y).iff (SyntaxVariableSyntax.code true w d y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := freeValue w d i y
    apply Derives.disjE (.hyp (Γ := Context.add E Γ) (Or.inl rfl))
    · exact .conjR (.hyp (Or.inl rfl))
    · let F := freeTail w i y
      let B := (successor i.castSucc (Fin.last m)).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) y.castSucc)
      let Δ := Context.add B (Context.image Formula.raise (Context.add F (Context.add E Γ)))
      apply Derives.exE (p := B) (.hyp (Or.inl rfl))
      have hi1 := of_eq (empty_rename i Fin.castSucc) (under (add (add hi E) F) B)
      have hB : Derives Δ B := .hyp (Or.inl rfl)
      exact .botE (successor_not_empty _ _ (.conjL hB) hi1)
  · exact .impI (.disjL (.conjI (add hi _) (.hyp (Or.inl rfl))))

theorem free_successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i k y : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (.mem k w)) (hi : Derives Γ (successor i k)) :
    Derives Γ ((freeValue w d i y).iff (SyntaxVariableSyntax.code false w k y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := freeValue w d i y
    apply Derives.disjE (.hyp (Γ := Context.add E Γ) (Or.inl rfl))
    · exact .botE (successor_not_empty i k (add (add hi E) _) (.conjL (.hyp (Or.inl rfl))))
    · let F := freeTail w i y
      let B := (successor i.castSucc (Fin.last m)).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) y.castSucc)
      let Δ := Context.add B (Context.image Formula.raise (Context.add F (Context.add E Γ)))
      apply Derives.exE (p := B) (.hyp (Or.inl rfl))
      have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add (add hw E) F) B)
      have hk1 : Derives Δ (.mem k.castSucc w.castSucc) := under (add (add hk E) F) B
      have hi1 := of_eq (successor_rename i k Fin.castSucc) (under (add (add hi E) F) B)
      have hB : Derives Δ B := .hyp (Or.inl rfl)
      have he := StructuralNodeCore.predecessor_unique (ZFContext.under (ZFContext.add (ZFContext.add hZ E) F) B) _ _ _ _ hw1 hk1 hi1 (.conjL hB)
      have ho := AbstractVariableIndex.code_index_subst false _ _ _ _ (eq_symm he) (.conjR hB)
      exact of_eq (SyntaxVariableSyntax.code_rename false w k y Fin.castSucc).symm ho
  · exact .impI (.disjR (intro_freeTail w i y k (add hi _) (.hyp (Or.inl rfl))))

theorem bound_below_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i x y : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (hi : Derives Γ (.mem i d)) :
    Derives Γ ((boundValue w d i x y).iff (.equal y x)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundValue w d i x y
    apply Derives.disjE (.hyp (Γ := Context.add E Γ) (Or.inl rfl))
    · exact .conjR (.hyp (Or.inl rfl))
    · let F := boundShifted w d i y
      let B := (successor (Fin.last m) i.castSucc).conj ((Formula.mem d.castSucc (Fin.last m)).conj
        (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) y.castSucc))
      let Δ := Context.add B (Context.image Formula.raise (Context.add F (Context.add E Γ)))
      apply Derives.exE (p := B) (.hyp (Or.inl rfl))
      have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add (add hw E) F) B)
      have hd1 : Derives Δ (.mem d.castSucc w.castSucc) := under (add (add hd E) F) B
      have hi1 : Derives Δ (.mem i.castSucc d.castSucc) := under (add (add hi E) F) B
      have hB : Derives Δ B := .hyp (Or.inl rfl)
      have hdi := NaturalOrderBasic.member_successor _ _ _ (.conjL hB) (.conjL (.conjR hB))
      exact .botE (NaturalOrderBasic.below_not_reverse (ZFContext.under (ZFContext.add (ZFContext.add hZ E) F) B) _ _ _ hw1 hd1 hdi hi1)
  · exact .impI (.disjL (.conjI (add hi _) (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.AbstractVariableSpecialization
