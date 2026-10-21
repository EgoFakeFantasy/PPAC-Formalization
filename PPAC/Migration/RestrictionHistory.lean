import PPAC.Migration.OrdinalRecursionSyntax
import PPAC.Migration.RestrictionAlgebra

/-! 同一个实际前段图在嵌套限制之间传输；不重新选择历史见证。 -/
namespace PPAC.Migration.RestrictionHistory
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax

/-- x⊆b时，f在x上的实际限制h也正是f在b上的限制g在x上的限制。 -/
theorem through {m} {Γ : Context m} (h g f b x : Fin m)
    (hs : Derives Γ (subset x b)) (hg : Derives Γ (restrict g f b)) (hh : Derives Γ (restrict h f x)) :
    Derives Γ (restrict h g x) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hs' : Derives Δ (subset x.castSucc b.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hs
  have hg' : Derives Δ (restrict g.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hg
  have hh' : Derives Δ (restrict h.castSucc f.castSucc x.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hh
  have hgm := restrict_at g.castSucc f.castSucc b.castSucc (Fin.last m) hg'
  have hhm := restrict_at h.castSucc f.castSucc x.castSucc (Fin.last m) hh'
  apply Derives.conjI
  · apply Derives.impI
    let M := Formula.mem (Fin.last m) h.castSucc
    let Ξ := Context.add M Δ
    have hpair : Derives Ξ ((Formula.mem (Fin.last m) f.castSucc).conj (entryOn x.castSucc (Fin.last m))) :=
      .impE (.conjL (add hhm _)) (.hyp (Or.inl rfl))
    have hb := RestrictionAlgebra.entry_subset_domain x.castSucc b.castSucc (Fin.last m) (add hs' M) (.conjR hpair)
    exact .conjI (.impE (.conjR (add hgm M)) (.conjI (.conjL hpair) hb)) (.conjR hpair)
  · apply Derives.impI
    let P := (Formula.mem (Fin.last m) g.castSucc).conj (entryOn x.castSucc (Fin.last m))
    have hp : Derives (Context.add P Δ) P := .hyp (Or.inl rfl)
    have hf := Derives.conjL (Derives.impE (.conjL (add hgm P)) (.conjL hp))
    exact .impE (.conjR (add hhm P)) (.conjI hf (.conjR hp))
end PPAC.Migration.RestrictionHistory
