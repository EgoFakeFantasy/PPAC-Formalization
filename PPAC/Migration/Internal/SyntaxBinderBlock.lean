import PPAC.Migration.Internal.ObjectSyntaxComposeLift

/-! 原allE逐个消去有限对象全称块；将大公式一次重命名，不增添推导核规则。 -/
namespace PPAC.Migration.Internal.SyntaxBinderBlock
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax

def block {m} : (k : Nat) → Formula (m+k) → Formula m
  | 0, p => p
  | k+1, p => block k (.all p)

theorem eliminate {m} {Γ : Context m} {k : Nat} (p : Formula (m+k)) (ρ : Fin (m+k) → Fin m)
    (fixed : ∀ i : Fin m, ρ (i.castAdd k) = i) (hp : Derives Γ (block k p)) : Derives Γ (p.rename ρ) := by
  induction k with
  | zero =>
      have hr : ρ = id := funext fixed
      exact of_eq (by simp only [block, hr, Reverse.source_rename_id]) hp
  | succ k ih =>
      let σ : Fin (m+k) → Fin m := fun i => ρ i.castSucc
      have hs : ∀ i : Fin m, σ (i.castAdd k) = i := fun i => fixed i
      have ha := ih (.all p) σ hs hp
      have he := Derives.allE (ρ (Fin.last (m+k))) ha
      have eqn : (p.rename (Formula.liftRen σ)).instantiate (ρ (Fin.last (m+k))) = p.rename ρ := by
        simp only [Formula.instantiate, rename_comp]
        congr 1
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Formula.liftRen, Fin.lastCases_last]
        · simp only [Formula.liftRen, Fin.lastCases_castSucc, σ, id_eq]
      exact of_eq eqn he
end PPAC.Migration.Internal.SyntaxBinderBlock
