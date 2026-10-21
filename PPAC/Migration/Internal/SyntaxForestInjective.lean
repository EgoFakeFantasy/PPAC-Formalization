import PPAC.Migration.Internal.ObjectSyntaxConstructors

/-! 同一原森林码反向恢复全部给定字段；不以同输入编码唯一性冒充此方向。 -/
namespace PPAC.Migration.Internal.SyntaxForestInjective
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax SyntaxForestSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem output_subst {m} {Γ : Context m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n r : Fin m)
    (he : Derives Γ (.equal n r)) (hn : Derives Γ (forest k w xs n)) : Derives Γ (forest k w xs r) := by
  have hi : Derives Γ ((forest k w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).instantiate n) := by
    simpa only [Formula.instantiate, forest_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hn
  have ho := Derives.eqSubst (forest k w.castSucc (fun i => (xs i).castSucc) (Fin.last m)) he hi
  simpa only [Formula.instantiate, forest_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem input_eq {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (forest k w xs n)) (hy : Derives Γ (forest k w ys n)) : Derives Γ (.equal (xs i) (ys i)) := by
  induction k generalizing m with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    let X := (Formula.mem (xs 0).castSucc w.castSucc).conj
      ((forest k w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m)).conj (consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))
    let Ξ := Context.add X (Context.image Formula.raise Γ)
    apply eliminate_cons k w xs n _ hx
    have hy1 : Derives Ξ (forest (k+1) w.castSucc (fun i => (ys i).castSucc) n.castSucc) := by simpa only [Formula.raise, forest_rename] using under hy X
    let Y := (Formula.mem (ys 0).castSucc.castSucc w.castSucc.castSucc).conj
      ((forest k w.castSucc.castSucc (fun i => (ys i.succ).castSucc.castSucc) (Fin.last (m+1))).conj
        (consCode w.castSucc.castSucc (ys 0).castSucc.castSucc (Fin.last (m+1)) n.castSucc.castSucc))
    let Δ := Context.add Y (Context.image Formula.raise Ξ)
    apply eliminate_cons k w.castSucc (fun i => (ys i).castSucc) n.castSucc _ hy1
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ X) Y
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw X) Y
    have hX : Derives Ξ X := .hyp (Or.inl rfl)
    have hX2 : Derives Δ ((Formula.mem (xs 0).castSucc.castSucc w.castSucc.castSucc).conj
        ((forest k w.castSucc.castSucc (fun i => (xs i.succ).castSucc.castSucc) (Fin.last m).castSucc).conj
          (consCode w.castSucc.castSucc (xs 0).castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc))) := by
      simpa only [X, Formula.raise, Formula.rename, forest_rename, consCode_rename] using under hX Y
    have hY : Derives Δ Y := .hyp (Or.inl rfl)
    have ht := SyntaxForests.range hZ2 k _ _ _ hw2 (.conjL (.conjR hX2))
    have hu := SyntaxForests.range hZ2 k _ _ _ hw2 (.conjL (.conjR hY))
    have heq := StructuralConsUnique.injective hZ2 _ _ _ _ _ _ hw2 (.conjL hX2) ht (.conjL hY) hu (.conjR (.conjR hX2)) (.conjR (.conjR hY))
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .conjL heq
    · have hyt := output_subst k _ _ _ _ (eq_symm (.conjR heq)) (.conjL (.conjR hY))
      exact ih hZ2 _ _ _ _ j hw2 (.conjL (.conjR hX2)) hyt
end PPAC.Migration.Internal.SyntaxForestInjective
