import PPAC.Migration.RestrictionHistory

/-! 任意参数递推条件沿传递初段限制保持，并实际构造受限递归图。 -/
namespace PPAC.Migration.OrdinalRecursionRestriction
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax OrdinalRecursionSyntax
open ReplacementPredicates (paramsUp)

def restrictedExists {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f b : Fin m) : Formula m := .ex
  ((restrict (Fin.last m) f.castSucc b.castSucc).conj (recursor p (paramsUp ρ) (Fin.last m) b.castSucc))

theorem restrictedExists_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f b : Fin m) (r : Fin m → Fin k) :
    (restrictedExists p ρ f b).rename r = restrictedExists p (fun i => r (ρ i)) (r f) (r b) := by
  simp only [restrictedExists, Formula.rename, restrict_rename, recursor_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem history_restrict {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g f b x y : Fin m)
    (hs : Derives Γ (subset x b)) (hg : Derives Γ (restrict g f b))
    (hh : Derives Γ (history p ρ f x y)) : Derives Γ (history p ρ g x y) := by
  let H := (restrict (Fin.last m) f.castSucc x.castSucc).conj
    (operator p (paramsUp ρ) x.castSucc (Fin.last m) y.castSucc)
  let Ξ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have hs' : Derives Ξ (subset x.castSucc b.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hs H
  have hg' : Derives Ξ (restrict g.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using under hg H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have hr := RestrictionHistory.through (Fin.last m) g.castSucc f.castSucc b.castSucc x.castSucc hs' hg' (.conjL hH)
  simpa only [Formula.raise, history_rename] using history_intro p (paramsUp ρ) g.castSucc x.castSucc (Fin.last m) y.castSucc hr (.conjR hH)

theorem equations_restrict {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g f b d : Fin m)
    (ht : Derives Γ (transitiveSet b)) (hs : Derives Γ (subset b d))
    (hg : Derives Γ (restrict g f b)) (hf : Derives Γ (equations p ρ f d)) : Derives Γ (equations p ρ g b) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have ht' : Derives Δ (transitiveSet b.castSucc) := by
    simpa only [Formula.raise, transitiveSet_rename] using Derives.rename Fin.castSucc ht
  have hs' : Derives Δ (subset b.castSucc d.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hs
  have hg' : Derives Δ (restrict g.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hg
  have hf' : Derives Δ (equations p (paramsUp ρ) f.castSucc d.castSucc) := by
    simpa only [Formula.raise, equations_rename] using Derives.rename Fin.castSucc hf
  apply Derives.impI
  let X := Formula.mem (Fin.last m) b.castSucc
  let Γx := Context.add X Δ
  have hx : Derives Γx X := .hyp (Or.inl rfl)
  have hxd : Derives Γx (.mem (Fin.last m) d.castSucc) := .impE (add (subset_at b.castSucc d.castSucc (Fin.last m) hs') _) hx
  have hxb := OrdinalTransitivity.subset_of_member b.castSucc (Fin.last m) (add ht' X) hx
  apply Derives.allI
  let Γy := Context.image Formula.raise Γx
  have hfY : Derives Γy (equations p (paramsUp (paramsUp ρ)) f.castSucc.castSucc d.castSucc.castSucc) := by
    simpa only [Formula.raise, equations_rename] using Derives.rename Fin.castSucc (add hf' X)
  have hgY : Derives Γy (restrict g.castSucc.castSucc f.castSucc.castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc (add hg' X)
  have hxdY : Derives Γy (.mem (Fin.last m).castSucc d.castSucc.castSucc) := Derives.rename Fin.castSucc hxd
  have hxbY : Derives Γy (subset (Fin.last m).castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hxb
  apply Derives.impI
  let E := edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add E Γy
  have he : Derives Ξ E := .hyp (Or.inl rfl)
  have hold := RestrictionEdges.old_edge g.castSucc.castSucc f.castSucc.castSucc b.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (add hgY E) he
  have hhist := Derives.impE (Derives.impE (add (equations_at p (paramsUp (paramsUp ρ))
    f.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hfY) E) (add hxdY E)) hold
  exact history_restrict p (paramsUp (paramsUp ρ)) g.castSucc.castSucc f.castSucc.castSucc b.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (add hxbY E) (add hgY E) hhist

theorem recursor_restrict {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g f b d : Fin m)
    (ht : Derives Γ (transitiveSet b)) (hs : Derives Γ (subset b d))
    (hg : Derives Γ (restrict g f b)) (hf : Derives Γ (recursor p ρ f d)) : Derives Γ (recursor p ρ g b) :=
  .conjI (RestrictionFunction.function_restrict g f d b (.conjL hf) hs hg)
    (equations_restrict p ρ g f b d ht hs hg (.conjR hf))

theorem exists_restricted {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f b d : Fin m)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (ht : Derives Γ (transitiveSet b)) (hs : Derives Γ (subset b d))
    (hf : Derives Γ (recursor p ρ f d)) : Derives Γ (restrictedExists p ρ f b) := by
  have hex := exists_restrict f b hsep
  let R := restrict (Fin.last m) f.castSucc b.castSucc
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hex
  apply Derives.exE (p := R) hex
  have ht' : Derives Ξ (transitiveSet b.castSucc) := by
    simpa only [Formula.raise, transitiveSet_rename] using under ht R
  have hs' : Derives Ξ (subset b.castSucc d.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hs R
  have hf' : Derives Ξ (recursor p (paramsUp ρ) f.castSucc d.castSucc) := by
    simpa only [Formula.raise, recursor_rename] using under hf R
  have hr : Derives Ξ R := .hyp (Or.inl rfl)
  have hrec := recursor_restrict p (paramsUp ρ) (Fin.last m) f.castSucc b.castSucc d.castSucc ht' hs' hr hf'
  have hout : Derives Ξ (restrictedExists p (paramsUp ρ) f.castSucc b.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, restrict_rename, recursor_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hr hrec
  simpa only [Formula.raise, restrictedExists_rename] using hout
end PPAC.Migration.OrdinalRecursionRestriction
