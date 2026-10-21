import PPAC.Migration.OrdinalComparison

/-! 三分支比较的两两排斥亦为对象推导，避免只给未排斥的析取。 -/
namespace PPAC.Migration.OrdinalTrichotomy
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalComparison OrdinalDifference

def trichotomy {m} (a b : Fin m) : Formula m := (comparison a b).conj
  (((Formula.equal a b).imp ((Formula.mem a b).neg.conj (Formula.mem b a).neg)).conj
    ((Formula.mem a b).imp (Formula.mem b a).neg))

theorem trichotomy_rename {m k} (a b : Fin m) (ρ : Fin m → Fin k) :
    (trichotomy a b).rename ρ = trichotomy (ρ a) (ρ b) := rfl

theorem equal_excludes {m} {Γ : Context m} (a b : Fin m)
    (ha : Derives Γ (ordinal a)) (he : Derives Γ (.equal a b)) :
    Derives Γ ((Formula.mem a b).neg.conj (Formula.mem b a).neg) := by
  have hn := OrdinalEmpty.no_self a (.conjL (.conjR ha))
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add hn _) (UnorderedPairLogic.mem_container_subst b a a (eq_symm (add he _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add hn _) (mem_subst (eq_symm (add he _)) (.hyp (Or.inl rfl)))

theorem prove {m} {Γ : Context m} (a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation outsideMatrix).rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hb : Derives Γ (ordinal b)) : Derives Γ (trichotomy a b) := by
  apply Derives.conjI (OrdinalComparison.compare a b he hf hs ha hb)
  apply Derives.conjI
  · apply Derives.impI
    exact equal_excludes a b (add ha _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact OrdinalComparison.asymmetric a b (add ha _) (.hyp (Or.inl rfl))
end PPAC.Migration.OrdinalTrichotomy
