import PPAC.Migration.RestrictionFunction

/-! 限制图的外延唯一性、恒等与迭代限制；全部为对象推导。 -/
namespace PPAC.Migration.RestrictionAlgebra
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic RestrictionSyntax OrderedPairElimination

theorem same_members {m} {Γ : Context m} (g h f b : Fin m)
    (hg : Derives Γ (restrict g f b)) (hh : Derives Γ (restrict h f b)) : Derives Γ (sameMembers g h) := by
  apply Derives.allI
  have hg' : Derives (Context.image Formula.raise Γ) (restrict g.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hg
  have hh' : Derives (Context.image Formula.raise Γ) (restrict h.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hh
  have hgm := restrict_at g.castSucc f.castSucc b.castSucc (Fin.last m) hg'
  have hhm := restrict_at h.castSucc f.castSucc b.castSucc (Fin.last m) hh'
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (.conjR (add hhm _)) (.impE (.conjL (add hgm _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (.conjR (add hgm _)) (.impE (.conjL (add hhm _)) (.hyp (Or.inl rfl)))

theorem unique {m} {Γ : Context m} (g h f b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (restrict g f b)) (hh : Derives Γ (restrict h f b)) : Derives Γ (.equal g h) :=
  .impE (extensionality_instance g h he) (same_members g h f b hg hh)

theorem identity {m} {Γ : Context m} (g f d : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hr : Derives Γ (restrict g f d)) : Derives Γ (.equal g f) := by
  apply Derives.impE (extensionality_instance g f he)
  apply Derives.allI
  have hf' : Derives (Context.image Formula.raise Γ) (functionOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc hf
  have hr' : Derives (Context.image Formula.raise Γ) (restrict g.castSucc f.castSucc d.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hr
  have hrm := restrict_at g.castSucc f.castSucc d.castSucc (Fin.last m) hr'
  apply Derives.conjI
  · apply Derives.impI
    exact .conjL (.impE (.conjL (add hrm _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let M := Formula.mem (Fin.last m) f.castSucc
    have hm : Derives (Context.add M (Context.image Formula.raise Γ)) M := .hyp (Or.inl rfl)
    have hc := Derives.impE (entries_at f.castSucc d.castSucc (Fin.last m) (.conjL (add hf' M))) hm
    exact .impE (.conjR (add hrm M)) (.conjI hm hc)

theorem entry_subset_domain {m} {Γ : Context m} (c b p : Fin m)
    (hs : Derives Γ (subset c b)) (hp : Derives Γ (entryOn c p)) : Derives Γ (entryOn b p) := by
  let A := entryWitnesses c p
  let Γa := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply entry_elim c p _ hp
  have hsA : Derives Γa (subset c.castSucc.castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under_two hs A
  have hA : Derives Γa A := .hyp (Or.inl rfl)
  have hb := Derives.impE (subset_at c.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc hsA) (.conjL hA)
  have ho := entry_intro b.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hb (.conjR hA)
  simpa only [Formula.raise, entryOn_rename] using ho

theorem compose {m} {Γ : Context m} (h g f b c : Fin m)
    (hs : Derives Γ (subset c b)) (hg : Derives Γ (restrict g f b)) (hh : Derives Γ (restrict h g c)) :
    Derives Γ (restrict h f c) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hs' : Derives Δ (subset c.castSucc b.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hs
  have hg' : Derives Δ (restrict g.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hg
  have hh' : Derives Δ (restrict h.castSucc g.castSucc c.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hh
  have hgm := restrict_at g.castSucc f.castSucc b.castSucc (Fin.last m) hg'
  have hhm := restrict_at h.castSucc g.castSucc c.castSucc (Fin.last m) hh'
  apply Derives.conjI
  · apply Derives.impI
    have hc := Derives.impE (.conjL (add hhm (Formula.mem (Fin.last m) h.castSucc))) (.hyp (Or.inl rfl))
    exact .conjI (.conjL (.impE (.conjL (add hgm _)) (.conjL hc))) (.conjR hc)
  · apply Derives.impI
    let E := (Formula.mem (Fin.last m) f.castSucc).conj (entryOn c.castSucc (Fin.last m))
    have hE : Derives (Context.add E Δ) E := .hyp (Or.inl rfl)
    have hb := entry_subset_domain c.castSucc b.castSucc (Fin.last m) (add hs' E) (.conjR hE)
    have hm := Derives.impE (.conjR (add hgm E)) (.conjI (.conjL hE) hb)
    exact .impE (.conjR (add hhm E)) (.conjI hm (.conjR hE))
end PPAC.Migration.RestrictionAlgebra
