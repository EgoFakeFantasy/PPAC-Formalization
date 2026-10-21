import PPAC.Migration.OrderedPairExistence

/-! Kuratowski两个存在见证的同时消去，目标仍由原exE规则组成。 -/
namespace PPAC.Migration.OrderedPairElimination
open Source PairSyntax

def bundle {m} (p x y s t : Fin m) : Formula m :=
  (pair s x x).conj ((pair t x y).conj (pair p s t))

theorem bundle_rename {m k} (p x y s t : Fin m) (r : Fin m → Fin k) :
    (bundle p x y s t).rename r = bundle (r p) (r x) (r y) (r s) (r t) := by
  simp only [bundle, Formula.rename, pair_rename]

abbrev witnesses {m} (p x y : Fin m) : Formula (m+2) :=
  bundle p.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1))

theorem eliminate {m} {Γ : Context m} (p x y : Fin m) (q : Formula m)
    (h : Derives Γ (ordered p x y))
    (hc : Derives (Context.add (witnesses p x y)
      (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) :
    Derives Γ q := by
  change Derives Γ (.ex (.ex (witnesses p x y))) at h
  apply Derives.exE h
  apply Derives.exE (p := witnesses p x y) (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  intro r hr
  rcases hr with hr | ⟨s, hs, he⟩
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr hs, he⟩

theorem under_two {m} {Γ : Context m} {q : Formula m} (h : Derives Γ q) (b : Formula (m+2)) :
    Derives (Context.add b (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise :=
  .weaken (fun _ h => Or.inr h) (.rename Fin.castSucc (.rename Fin.castSucc h))
end PPAC.Migration.OrderedPairElimination
