import PPAC.Migration.Internal.SyntaxForests

/-! 精确k字段原森林的实际长度就是对象数码k；字段数不靠宿主解码器断言。 -/
namespace PPAC.Migration.Internal.SyntaxForestLength
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax SyntaxForestSyntax SyntaxNumeralSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_numeral {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n l : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (forest k w xs n)) (hl : Derives Γ (numeral k l)) : Derives Γ (hasLength w n l) := by
  induction k generalizing m with
  | zero => exact StructuralListLengthConstruct.nil_length hZ _ _ _ hw hn hl
  | succ k ih =>
    let C := (Formula.mem (xs 0).castSucc w.castSucc).conj
      ((forest k w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m)).conj (consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))
    let Ξ := Context.add C (Context.image Formula.raise Γ)
    apply eliminate_cons k w xs n _ hn
    have hl1 : Derives Ξ (numeral (k+1) l.castSucc) := by simpa only [Formula.raise, numeral_rename] using under hl C
    let L := (numeral k (Fin.last (m+1))).conj (successor l.castSucc.castSucc (Fin.last (m+1)))
    let Δ := Context.add L (Context.image Formula.raise Ξ)
    apply eliminate_succ k l.castSucc _ hl1
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ C) L
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw C) L
    have hC : Derives Ξ C := .hyp (Or.inl rfl)
    have hC2 : Derives Δ ((Formula.mem (xs 0).castSucc.castSucc w.castSucc.castSucc).conj
        ((forest k w.castSucc.castSucc (fun i => (xs i.succ).castSucc.castSucc) (Fin.last m).castSucc).conj
          (consCode w.castSucc.castSucc (xs 0).castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc))) := by
      simpa only [C, Formula.raise, Formula.rename, forest_rename, consCode_rename] using under hC L
    have hL : Derives Δ L := .hyp (Or.inl rfl)
    have ht := ih hZ2 _ _ _ _ hw2 (.conjL (.conjR hC2)) (.conjL hL)
    have hout := StructuralListLengthConstruct.cons_length hZ2 _ _ _ _ _ _ hw2 (.conjL hC2) (.conjR (.conjR hC2)) ht (.conjR hL)
    simpa only [Formula.raise, hasLength_rename] using hout
end PPAC.Migration.Internal.SyntaxForestLength
