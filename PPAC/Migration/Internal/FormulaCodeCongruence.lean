import PPAC.Migration.Internal.FormulaCodeRecursiveSyntax

/-! 原19规则中的合取/存在双条件同余；新鲜末变量保持原绑定约定。 -/
namespace PPAC.Migration.Internal.FormulaCodeCongruence
open Source SourceAlgebra SourceLogic

theorem conj_congr {m} {Γ : Context m} {p p' q q' : Formula m}
    (hp : Derives Γ (p.iff p')) (hq : Derives Γ (q.iff q')) :
    Derives Γ ((p.conj q).iff (p'.conj q')) := by
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (.impE (add (.conjL hp) _) (.conjL (.hyp (Or.inl rfl))))
      (.impE (add (.conjL hq) _) (.conjR (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact .conjI (.impE (add (.conjR hp) _) (.conjL (.hyp (Or.inl rfl))))
      (.impE (add (.conjR hq) _) (.conjR (.hyp (Or.inl rfl))))

theorem ex_raise_instance {m} (p : Formula (m+1)) :
    (p.rename (Formula.liftRen (Fin.castSucc : Fin m → Fin (m+1)))).instantiate (Fin.last m) = p := by
  simp only [Formula.instantiate, rename_comp]
  have h : (fun i : Fin (m+1) => Fin.lastCases (Fin.last m) id (Formula.liftRen Fin.castSucc i)) = id := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  rw [h, Reverse.source_rename_id]

theorem ex_congr {m} {Γ : Context m} {p q : Formula (m+1)}
    (hh : Derives (Context.image Formula.raise Γ) (p.iff q)) :
    Derives Γ ((Formula.ex p).iff (.ex q)) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.exE (.hyp (Or.inl rfl))
    apply Derives.exI (Fin.last m)
    rw [ex_raise_instance]
    apply Derives.impE _ (.hyp (Or.inl rfl))
    apply Derives.weaken _ (.conjL hh)
    rintro s ⟨t, ht, he⟩
    exact Or.inr ⟨t, Or.inr ht, he⟩
  · apply Derives.impI
    apply Derives.exE (.hyp (Or.inl rfl))
    apply Derives.exI (Fin.last m)
    rw [ex_raise_instance]
    apply Derives.impE _ (.hyp (Or.inl rfl))
    apply Derives.weaken _ (.conjR hh)
    rintro s ⟨t, ht, he⟩
    exact Or.inr ⟨t, Or.inr ht, he⟩
end PPAC.Migration.Internal.FormulaCodeCongruence
