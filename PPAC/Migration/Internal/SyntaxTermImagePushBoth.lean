import PPAC.Migration.Internal.SyntaxTermImagePushGraph

/-! 两张实际项像表同时逐值变换；旧bound和旧free项像均经过目标重命名。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePushBoth
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxTermImagePushSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def both {m} (w R S c d C D r s a b g h : Fin m) : Formula m := (pushed w R S c d C D r a g).conj (pushed w R S c d C D s b h)

def tail {m} (w R S c d C D r s a b g : Fin m) : Formula m := .ex (both w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc r.castSucc s.castSucc a.castSucc b.castSucc g.castSucc (Fin.last m))

def existsBoth {m} (w R S c d C D r s a b : Fin m) : Formula m := .ex (tail w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc r.castSucc s.castSucc a.castSucc b.castSucc (Fin.last m))

theorem both_rename {m k} (w R S c d C D r s a b g h : Fin m) (ρ : Fin m → Fin k) :
    (both w R S c d C D r s a b g h).rename ρ = both (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ r) (ρ s) (ρ a) (ρ b) (ρ g) (ρ h) := by
  simp only [both, Formula.rename, pushed_rename]

theorem tail_rename {m k} (w R S c d C D r s a b g : Fin m) (ρ : Fin m → Fin k) :
    (tail w R S c d C D r s a b g).rename ρ = tail (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ r) (ρ s) (ρ a) (ρ b) (ρ g) := by
  simp only [tail, Formula.rename, both_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsBoth_rename {m k} (w R S c d C D r s a b : Fin m) (ρ : Fin m → Fin k) :
    (existsBoth w R S c d C D r s a b).rename ρ = existsBoth (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ r) (ρ s) (ρ a) (ρ b) := by
  simp only [existsBoth, Formula.rename, tail_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_tail {m} {Γ : Context m} (w R S c d C D r s a b g h : Fin m)
    (hh : Derives Γ (both w R S c d C D r s a b g h)) : Derives Γ (tail w R S c d C D r s a b g) := by
  apply Derives.exI h
  exact of_eq (by simp only [Formula.instantiate, both_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem intro_exists {m} {Γ : Context m} (w R S c d C D r s a b g h : Fin m)
    (hh : Derives Γ (both w R S c d C D r s a b g h)) : Derives Γ (existsBoth w R S c d C D r s a b) := by
  apply Derives.exI g
  exact of_eq (by simp only [Formula.instantiate, tail_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (intro_tail w R S c d C D r s a b g h hh)

theorem exists_both {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D r s a b : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxIndexMapSyntax.maps w R S c d C D))
    (hi : Derives Γ (SyntaxTermImageSyntax.maps w r s a b c d)) :
    Derives Γ (existsBoth w R S c d C D r s a b) := by
  let G := pushed w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc r.castSucc a.castSucc (Fin.last m)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (SyntaxTermImagePushGraph.exists_push hZ w R S c d C D r a hw (.conjL hi) hm)
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw G)
  have hm1 : Derives Ξ (SyntaxIndexMapSyntax.maps w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc) := of_eq (SyntaxIndexMapSyntax.maps_rename w R S c d C D Fin.castSucc) (under hm G)
  have hs1 : Derives Ξ (imageMap w.castSucc s.castSucc b.castSucc c.castSucc d.castSucc) := of_eq (imageMap_rename w s b c d Fin.castSucc) (under (.conjR hi) G)
  let H := pushed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc D.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) (SyntaxTermImagePushGraph.exists_push (ZFContext.under hZ G) w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc s.castSucc b.castSucc hw1 hs1 hm1)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hg2 : Derives Δ (pushed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc D.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [G, Formula.raise, pushed_rename]) (under hG H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have ho := intro_exists w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc D.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjI hg2 hH)
  exact of_eq (by simp only [Formula.raise, existsBoth_rename]) ho

theorem target_maps {m} {Γ : Context m} (w R S c d C D r s a b g h : Fin m)
    (hh : Derives Γ (both w R S c d C D r s a b g h)) : Derives Γ (SyntaxTermImageSyntax.maps w g h a b C D) :=
  .conjI (.conjL (.conjR (.conjR (.conjL hh)))) (.conjL (.conjR (.conjR (.conjR hh))))

theorem unique_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D r s a b g h G H : Fin m)
    (hh : Derives Γ (both w R S c d C D r s a b g h)) (hH : Derives Γ (both w R S c d C D r s a b G H)) :
    Derives Γ ((Formula.equal g G).conj (Formula.equal h H)) :=
  .conjI (SyntaxTermImagePushGraph.unique hZ w R S c d C D r a g G (.conjL hh) (.conjL hH))
    (SyntaxTermImagePushGraph.unique hZ w R S c d C D s b h H (.conjR hh) (.conjR hH))

end PPAC.Migration.Internal.SyntaxTermImagePushBoth
