import PPAC.Migration.OrdinalDifference

/-! 原序数的每个传递子集等于该序数或属于该序数；全对象初段推导。 -/
namespace PPAC.Migration.OrdinalInitialSegment
open Source SourceAlgebra SourceLogic RestrictionSyntax OrdinalSyntax OrdinalDifference

theorem subset_minimal {m} {Γ : Context m} (a b u : Fin m)
    (hb : Derives Γ (transitiveSet b)) (hs : Derives Γ (subset b a))
    (hc : Derives Γ (comparable a)) (hm : Derives Γ (minimal a b u)) : Derives Γ (subset b u) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hb' : Derives Δ (transitiveSet b.castSucc) := by
    simpa only [Formula.raise, transitiveSet_rename] using Derives.rename Fin.castSucc hb
  have hs' : Derives Δ (subset b.castSucc a.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hs
  have hc' : Derives Δ (comparable a.castSucc) := by
    simpa only [Formula.raise, comparable_rename] using Derives.rename Fin.castSucc hc
  have hm' : Derives Δ (minimal a.castSucc b.castSucc u.castSucc) := by
    simpa only [Formula.raise, minimal_rename] using Derives.rename Fin.castSucc hm
  apply Derives.impI
  let Ξ := Context.add (.mem (Fin.last m) b.castSucc) Δ
  have hvb : Derives Ξ (.mem (Fin.last m) b.castSucc) := .hyp (Or.inl rfl)
  have hva : Derives Ξ (.mem (Fin.last m) a.castSucc) :=
    .impE (add (subset_at b.castSucc a.castSucc (Fin.last m) hs') _) hvb
  have hua : Derives Ξ (.mem u.castSucc a.castSucc) := .conjL (.conjL (add hm' _))
  have hnu : Derives Ξ (Formula.mem u.castSucc b.castSucc).neg := .conjR (.conjL (add hm' _))
  have hcmp := Derives.impE (Derives.impE (add (comparable_at a.castSucc (Fin.last m) u.castSucc hc') _) hva) hua
  apply Derives.disjE hcmp
  · exact .botE (.impE (add hnu _) (mem_subst (.hyp (Or.inl rfl)) (add hvb _)))
  · apply Derives.disjE (Derives.hyp (Or.inl rfl))
    · exact .hyp (Or.inl rfl)
    · have hub : Derives (Context.add (.mem u.castSucc (Fin.last m))
          (Context.add ((Formula.mem (Fin.last m) u.castSucc).disj (.mem u.castSucc (Fin.last m))) Ξ))
          (.mem u.castSucc b.castSucc) :=
        .impE (.impE (add (add (add (transitiveSet_at b.castSucc (Fin.last m) u.castSucc hb') _) _) _)
          (add (add hvb _) _)) (.hyp (Or.inl rfl))
      exact .botE (.impE (add (add hnu _) _) hub)

theorem equal_minimal {m} {Γ : Context m} (a b u : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hb : Derives Γ (transitiveSet b))
    (hs : Derives Γ (subset b a)) (hm : Derives Γ (minimal a b u)) : Derives Γ (.equal b u) :=
  OmegaAlgebra.subset_antisymm b u he
    (subset_minimal a b u hb hs (.conjR (.conjR (.conjL (.conjR ha)))) hm)
    (minimal_subset a b u (.conjL ha) hm)

theorem proper_member {m} {Γ : Context m} (a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation outsideMatrix).rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hb : Derives Γ (transitiveSet b))
    (hs : Derives Γ (subset b a)) (hn : Derives Γ (subset a b).neg) : Derives Γ (.mem b a) := by
  have hex := exists_minimal a b hsep hf (has_of_not_subset a b hn)
  let M := minimal a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add M (Context.image Formula.raise Γ)
  apply Derives.exE (p := M) hex
  have he' : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he M
  have ha' : Derives Ξ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha M
  have hb' : Derives Ξ (transitiveSet b.castSucc) := by
    simpa only [Formula.raise, transitiveSet_rename] using under hb M
  have hs' : Derives Ξ (subset b.castSucc a.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hs M
  have hm : Derives Ξ M := .hyp (Or.inl rfl)
  have heq := equal_minimal a.castSucc b.castSucc (Fin.last m) he' ha' hb' hs' hm
  exact mem_subst (eq_symm heq) (.conjL (.conjL hm))

/-- 双向包含分支由外延性给相等；否则实际取差性质极小元。 -/
theorem initial_segment {m} {Γ : Context m} (a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation outsideMatrix).rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hb : Derives Γ (transitiveSet b))
    (hs : Derives Γ (subset b a)) : Derives Γ ((Formula.equal b a).disj (.mem b a)) := by
  apply Derives.classical
  let R := (Formula.equal b a).disj (.mem b a)
  let Δ := Context.add R.neg Γ
  have hno : Derives Δ R.neg := .hyp (Or.inl rfl)
  have hn : Derives Δ (subset a b).neg := by
    apply Derives.impI
    have heq : Derives (Context.add (subset a b) Δ) (.equal b a) := OmegaAlgebra.subset_antisymm b a (add (add he _) _) (add (add hs _) _) (.hyp (Or.inl rfl))
    exact .impE (add hno _) (.disjL heq)
  have hmem := proper_member a b (add he _) (add hf _) (add hsep _) (add ha _) (add hb _) (add hs _) hn
  exact .impE hno (.disjR hmem)
end PPAC.Migration.OrdinalInitialSegment
