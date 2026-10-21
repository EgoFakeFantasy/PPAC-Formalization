import PPAC.Migration.Internal.SyntaxNumeralMembers

/-! 任意原森林的每个合法数码位置精确读取原字段；位置和值候选均为内部变量。 -/
namespace PPAC.Migration.Internal.SyntaxForestFieldValues
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForestSyntax SyntaxNumeralSyntax StructuralListSyntax StructuralListFieldSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem field_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m)
    (xs : Fin k → Fin m) (n : Fin m) (j : Fin k) (i y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (forest k w xs n)) (hi : Derives Γ (numeral j.val i)) :
    Derives Γ ((field w n i y).iff (.equal y (xs j))) := by
  induction k generalizing m with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    revert hi
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hi
      let C := (Formula.mem (xs 0).castSucc w.castSucc).conj
        ((forest k w.castSucc (fun j => (xs j.succ).castSucc) (Fin.last m)).conj
          (consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))
      let Δ := Context.add C (Context.image Formula.raise Γ)
      apply eliminate_cons k w xs n _ hf
      have hZ1 := ZFContext.under hZ C
      have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
      have hi1 : Derives Δ (empty i.castSucc) := by simpa only [Formula.raise, numeral_rename, Fin.val_zero, numeral, empty_rename] using under hi C
      have hC : Derives Δ C := .hyp (Or.inl rfl)
      have ht := SyntaxForests.range hZ1 k w.castSucc (fun j => (xs j.succ).castSucc) (Fin.last m) hw1 (.conjL (.conjR hC))
      have hout := StructuralListFieldCons.zero_iff hZ1 w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc i.castSucc y.castSucc hw1 (.conjL hC) ht (.conjR (.conjR hC)) hi1
      simpa only [Formula.raise, Formula.iff, Formula.rename, field_rename] using hout
    · intro hi
      let C := (Formula.mem (xs 0).castSucc w.castSucc).conj
        ((forest k w.castSucc (fun j => (xs j.succ).castSucc) (Fin.last m)).conj
          (consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))
      let Δ := Context.add C (Context.image Formula.raise Γ)
      apply eliminate_cons k w xs n _ hf
      have hi1 : Derives Δ (numeral (j.val+1) i.castSucc) := by
        simpa only [Formula.raise, numeral_rename, Fin.val_succ] using under hi C
      let I := (numeral j.val (Fin.last (m+1))).conj (successor i.castSucc.castSucc (Fin.last (m+1)))
      let Ξ := Context.add I (Context.image Formula.raise Δ)
      apply eliminate_succ j.val i.castSucc _ hi1
      have hZ2 := ZFContext.under (ZFContext.under hZ C) I
      have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw C) I
      have hC : Derives Δ C := .hyp (Or.inl rfl)
      have hC2 : Derives Ξ ((Formula.mem (xs 0).castSucc.castSucc w.castSucc.castSucc).conj
          ((forest k w.castSucc.castSucc (fun a => (xs a.succ).castSucc.castSucc) (Fin.last m).castSucc).conj
            (consCode w.castSucc.castSucc (xs 0).castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc))) := by
        simpa only [C, Formula.raise, Formula.rename, forest_rename, consCode_rename] using under hC I
      have hI : Derives Ξ I := .hyp (Or.inl rfl)
      have ht := SyntaxForests.range hZ2 k _ _ _ hw2 (.conjL (.conjR hC2))
      have hp := SyntaxNumerals.range hZ2 j.val _ _ hw2 (.conjL hI)
      have hs := StructuralListFieldCons.successor_iff hZ2 w.castSucc.castSucc (xs 0).castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (Fin.last (m+1)) i.castSucc.castSucc y.castSucc.castSucc hw2 (.conjL hC2) ht hp (.conjR hI) (.conjR (.conjR hC2))
      have hh := ih hZ2 w.castSucc.castSucc (fun a => (xs a.succ).castSucc.castSucc) (Fin.last m).castSucc j
        (Fin.last (m+1)) y.castSucc.castSucc hw2 (.conjL (.conjR hC2)) (.conjL hI)
      have hout := SyntaxTypeLocalTransfer.iff_trans hs hh
      simpa only [Formula.raise, Formula.iff, Formula.rename, field_rename] using hout
end PPAC.Migration.Internal.SyntaxForestFieldValues
