import PPAC.Migration.Internal.SyntaxMixedImageLiftUnique

/-! 完整混合binder状态的实际存在：目标映射、零、原bvar0码及两张输出表均由对象量词构造。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageLiftState
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def snapshot {m} (w r s a b c d A C R S z n : Fin m) : Formula m :=
  (SyntaxFreeShiftSyntax.shiftMap w c C R).conj ((SyntaxIdentityMapSyntax.identityMap w d S).conj
    ((SyntaxMixedImageHead.head w C d z n).conj (SyntaxMixedImageLiftSyntax.existsPair w R S r s a b c d A C n)))

def headTail {m} (w r s a b c d A C R S z : Fin m) : Formula m := .ex
  (snapshot w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc R.castSucc S.castSucc z.castSucc (Fin.last m))

def heads {m} (w r s a b c d A C R S : Fin m) : Formula m := .ex
  (headTail w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc R.castSucc S.castSucc (Fin.last m))

def mapTail {m} (w r s a b c d A C R : Fin m) : Formula m := .ex
  (heads w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc R.castSucc (Fin.last m))

def existsState {m} (w r s a b c d A C : Fin m) : Formula m := .ex (mapTail w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc (Fin.last m))

theorem snapshot_rename {m j} (w r s a b c d A C R S z n : Fin m) (ρ : Fin m → Fin j) :
    (snapshot w r s a b c d A C R S z n).rename ρ = snapshot (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ R) (ρ S) (ρ z) (ρ n) := by
  simp only [snapshot, Formula.rename, SyntaxFreeShiftSyntax.shiftMap_rename, SyntaxIdentityMapSyntax.identityMap_rename, SyntaxMixedImageHead.head_rename, SyntaxMixedImageLiftSyntax.existsPair_rename]

theorem headTail_rename {m j} (w r s a b c d A C R S z : Fin m) (ρ : Fin m → Fin j) :
    (headTail w r s a b c d A C R S z).rename ρ = headTail (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ R) (ρ S) (ρ z) := by
  simp only [headTail, Formula.rename, snapshot_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem heads_rename {m j} (w r s a b c d A C R S : Fin m) (ρ : Fin m → Fin j) :
    (heads w r s a b c d A C R S).rename ρ = heads (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ R) (ρ S) := by
  simp only [heads, Formula.rename, headTail_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem mapTail_rename {m j} (w r s a b c d A C R : Fin m) (ρ : Fin m → Fin j) :
    (mapTail w r s a b c d A C R).rename ρ = mapTail (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ R) := by
  simp only [mapTail, Formula.rename, heads_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsState_rename {m j} (w r s a b c d A C : Fin m) (ρ : Fin m → Fin j) :
    (existsState w r s a b c d A C).rename ρ = existsState (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) := by
  simp only [existsState, Formula.rename, mapTail_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_head {m} {Γ : Context m} (w r s a b c d A C R S z n : Fin m)
    (hs : Derives Γ (snapshot w r s a b c d A C R S z n)) : Derives Γ (headTail w r s a b c d A C R S z) := by
  apply Derives.exI n
  exact of_eq (by simp only [Formula.instantiate, snapshot_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hs

theorem intro_heads {m} {Γ : Context m} (w r s a b c d A C R S z n : Fin m)
    (hs : Derives Γ (snapshot w r s a b c d A C R S z n)) : Derives Γ (heads w r s a b c d A C R S) := by
  apply Derives.exI z
  exact of_eq (by simp only [Formula.instantiate, headTail_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (intro_head w r s a b c d A C R S z n hs)

theorem intro_maps {m} {Γ : Context m} (w r s a b c d A C R S z n : Fin m)
    (hs : Derives Γ (snapshot w r s a b c d A C R S z n)) : Derives Γ (mapTail w r s a b c d A C R) := by
  apply Derives.exI S
  exact of_eq (by simp only [Formula.instantiate, heads_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (intro_heads w r s a b c d A C R S z n hs)

theorem intro_exists {m} {Γ : Context m} (w r s a b c d A C R S z n : Fin m)
    (hs : Derives Γ (snapshot w r s a b c d A C R S z n)) : Derives Γ (existsState w r s a b c d A C ) := by
  apply Derives.exI R
  exact of_eq (by simp only [Formula.instantiate, mapTail_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (intro_maps w r s a b c d A C R S z n hs)

theorem exists_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTermImageSyntax.maps w r s a b c d))
    (hA : Derives Γ (successor A a)) (hC : Derives Γ (successor C c)) :
    Derives Γ (existsState w r s a b c d A C) := by
  let B := (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc c.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc).conj
    ((SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))).conj
      (SyntaxTermImagePushBoth.existsBoth w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc))
  let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he : Derives Γ (.ex (.ex B)) := SyntaxTermImageBoundShift.exists_shift hZ w r s a b c d C hw hi hC
  apply SyntaxRenameBinders.eliminate_2 B _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hi2 : Derives Ξ (SyntaxTermImageSyntax.maps w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.maps_rename]) (SyntaxRenameBinders.under_2 hi B)
  have hA2 : Derives Ξ (successor A.castSucc.castSucc a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hA B)
  have hC2 : Derives Ξ (successor C.castSucc.castSucc c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hC B)
  have hcd := SyntaxTermImageSyntax.target_contexts w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc hi2
  let H := SyntaxMixedImageHead.head w.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Ξ))
  have hh : Derives Ξ (.ex (.ex H)) := SyntaxMixedImageHead.exists_head hZ2 w.castSucc.castSucc c.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc hw2 (.conjL hcd) (.conjR hcd) hC2
  apply SyntaxRenameBinders.eliminate_2 H _ hh
  have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 H
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw2 H)
  have hi4 : Derives Δ (SyntaxTermImageSyntax.maps w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.maps_rename]) (SyntaxRenameBinders.under_2 hi2 H)
  have hA4 : Derives Δ (successor A.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hA2 H)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb4 : Derives Δ ((SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc).conj
    ((SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc).conj
      (SyntaxTermImagePushBoth.existsBoth w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc))) :=
    of_eq (by simp only [B, Formula.raise, Formula.rename, SyntaxFreeShiftSyntax.shiftMap_rename, SyntaxIdentityMapSyntax.identityMap_rename, SyntaxTermImagePushBoth.existsBoth_rename]) (SyntaxRenameBinders.under_2 hB H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hm : Derives Δ (SyntaxIndexMapSyntax.maps w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc) :=
    .conjI (.conjL (.conjR (.conjL hb4))) (.conjL (.conjL (.conjR hb4)))
  have hp := SyntaxMixedImageLiftExistence.exists_pair hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) hw4 hi4 hm (.conjR (.conjR hH)) hA4
  have hs : Derives Δ (snapshot w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))) :=
    .conjI (.conjL hb4) (.conjI (.conjL (.conjR hb4)) (.conjI hH hp))
  have ho := intro_exists w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hs
  exact of_eq (by simp only [Formula.raise, existsState_rename]) ho

end PPAC.Migration.Internal.SyntaxMixedImageLiftState
