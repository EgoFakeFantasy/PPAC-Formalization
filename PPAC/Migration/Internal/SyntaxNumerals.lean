import PPAC.Migration.Internal.SyntaxNumeralSyntax

/-! 每个有限标签的实际内部自然数码存在唯一；不是宿主自然数到对象数据的选择函数。 -/
namespace PPAC.Migration.Internal.SyntaxNumerals
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNumeralSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (x y : Fin m)
    (hx : Derives Γ (numeral k x)) (hy : Derives Γ (numeral k y)) : Derives Γ (.equal x y) := by
  induction k generalizing m with
  | zero => exact OmegaUniversal.empty_unique x y (ZFContext.arithmetic hZ).base.extensionality hx hy
  | succ k ih =>
    let X := (numeral k (Fin.last m)).conj (successor x.castSucc (Fin.last m))
    let Ξ := Context.add X (Context.image Formula.raise Γ)
    apply eliminate_succ k x _ hx
    have hy1 : Derives Ξ (numeral (k+1) y.castSucc) := by simpa only [Formula.raise, numeral_rename] using under hy X
    let Y := (numeral k (Fin.last (m+1))).conj (successor y.castSucc.castSucc (Fin.last (m+1)))
    let Δ := Context.add Y (Context.image Formula.raise Ξ)
    apply eliminate_succ k y.castSucc _ hy1
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ X) Y
    have hX : Derives Ξ X := .hyp (Or.inl rfl)
    have hX2 : Derives Δ ((numeral k (Fin.last m).castSucc).conj (successor x.castSucc.castSucc (Fin.last m).castSucc)) := by
      simpa only [X, Formula.raise, Formula.rename, numeral_rename, successor_rename] using under hX Y
    have hY : Derives Δ Y := .hyp (Or.inl rfl)
    have heq := ih hZ2 _ _ (.conjL hX2) (.conjL hY)
    have hs := GodelUnpairArithmetic.successor_base_subst _ _ _ heq (.conjR hX2)
    exact OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ2).base.extensionality hs (.conjR hY)

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w x : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (numeral k x)) : Derives Γ (.mem x w) := by
  induction k generalizing m with
  | zero => exact OmegaStructureAlgebra.zero_member w x (ZFContext.arithmetic hZ).base.extensionality hw hx
  | succ k ih =>
    let X := (numeral k (Fin.last m)).conj (successor x.castSucc (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply eliminate_succ k x _ hx
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ X
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw X
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    exact OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ1).base.extensionality hw1 (ih hZ1 _ _ hw1 (.conjL hX)) (.conjR hX)

theorem exists_numeral {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsNumeral w k) := by
  induction k generalizing m with
  | zero => exact .conjL (.conjL hw)
  | succ k ih =>
    have hp := ih hZ w hw
    let P := (Formula.mem (Fin.last m) w.castSucc).conj (numeral k (Fin.last m))
    let Ξ := Context.add P (Context.image Formula.raise Γ)
    change Derives Γ (.ex P) at hp
    apply Derives.exE (p := P) hp
    have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ P
    have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
    have hP : Derives Ξ P := .hyp (Or.inl rfl)
    have hs := InsertExistence.exists_insert (Fin.last m) (Fin.last m) (ZFContext.arithmetic hZ1).base.pairing (ZFContext.arithmetic hZ1).base.union
    let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
    let Δ := Context.add S (Context.image Formula.raise Ξ)
    change Derives Ξ (.ex S) at hs
    apply Derives.exE (p := S) hs
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 S
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 S
    have hP2 : Derives Δ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (numeral k (Fin.last m).castSucc)) := by
      simpa only [P, Formula.raise, Formula.rename, numeral_rename] using under hP S
    have hS : Derives Δ S := .hyp (Or.inl rfl)
    have hnat := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ2).base.extensionality hw2 (.conjL hP2) hS
    have hnum := intro_succ k _ _ (.conjR hP2) hS
    have hout : Derives Δ (existsNumeral w.castSucc.castSucc (k+1)) := by
      apply Derives.exI (Fin.last (m+1))
      simp only [Formula.instantiate, Formula.rename, numeral_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      exact .conjI hnat hnum
    simpa only [Formula.raise, existsNumeral_rename] using hout

theorem less {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (i j : Nat) (hij : i < j) (x y : Fin m)
    (hx : Derives Γ (numeral i x)) (hy : Derives Γ (numeral j y)) : Derives Γ (.mem x y) := by
  induction j generalizing i m with
  | zero => omega
  | succ j ih =>
    let Y := (numeral j (Fin.last m)).conj (successor y.castSucc (Fin.last m))
    let Δ := Context.add Y (Context.image Formula.raise Γ)
    apply eliminate_succ j y _ hy
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Y
    have hx1 : Derives Δ (numeral i x.castSucc) := by simpa only [Formula.raise, numeral_rename] using under hx Y
    have hY : Derives Δ Y := .hyp (Or.inl rfl)
    by_cases he : i = j
    · subst i
      have heq := unique hZ1 j _ _ hx1 (.conjL hY)
      exact mem_subst (eq_symm heq) (InsertLogic.new_member _ _ _ (.conjR hY))
    · have hij' : i < j := by omega
      exact InsertLogic.old_member _ _ _ _ (.conjR hY) (ih hZ1 i hij' _ _ hx1 (.conjL hY))
theorem different {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (i j : Nat) (hij : i ≠ j) (x y : Fin m)
    (hx : Derives Γ (numeral i x)) (hy : Derives Γ (numeral j y)) : Derives Γ (Formula.equal x y).neg := by
  apply Derives.impI
  let E := Formula.equal x y
  have he : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.add hZ E
  by_cases hlt : i < j
  · have hm := less hZ1 i j hlt x y (add hx E) (add hy E)
    exact .impE (NaturalOrderBasic.nonself hZ1 x) (UnorderedPairLogic.mem_container_subst y x x (eq_symm he) hm)
  · have hgt : j < i := by omega
    have hm := less hZ1 j i hgt y x (add hy E) (add hx E)
    exact .impE (NaturalOrderBasic.nonself hZ1 x) (mem_subst (eq_symm he) hm)
end PPAC.Migration.Internal.SyntaxNumerals
