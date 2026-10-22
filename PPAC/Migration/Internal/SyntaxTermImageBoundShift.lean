import PPAC.Migration.Internal.SyntaxTermImagePushBoth
import PPAC.Migration.Internal.SyntaxFreeShiftGraph
import PPAC.Migration.Internal.SyntaxIdentityGraph

/-! 实际构造目标bound整体后移、目标free恒等时的两张变换表；尚未加入新的源bound0。 -/
namespace PPAC.Migration.Internal.SyntaxTermImageBoundShift
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def state {m} (w r s a b c d C R S : Fin m) : Formula m :=
  (SyntaxFreeShiftSyntax.shiftMap w c C R).conj ((SyntaxIdentityMapSyntax.identityMap w d S).conj
    (SyntaxTermImagePushBoth.existsBoth w R S c d C d r s a b))

def tail {m} (w r s a b c d C R : Fin m) : Formula m := .ex (state w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc C.castSucc R.castSucc (Fin.last m))

def existsShift {m} (w r s a b c d C : Fin m) : Formula m := .ex (tail w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc C.castSucc (Fin.last m))

theorem state_rename {m k} (w r s a b c d C R S : Fin m) (ρ : Fin m → Fin k) :
    (state w r s a b c d C R S).rename ρ = state (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ C) (ρ R) (ρ S) := by
  simp only [state, Formula.rename, SyntaxFreeShiftSyntax.shiftMap_rename, SyntaxIdentityMapSyntax.identityMap_rename, SyntaxTermImagePushBoth.existsBoth_rename]

theorem tail_rename {m k} (w r s a b c d C R : Fin m) (ρ : Fin m → Fin k) :
    (tail w r s a b c d C R).rename ρ = tail (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ C) (ρ R) := by
  simp only [tail, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsShift_rename {m k} (w r s a b c d C : Fin m) (ρ : Fin m → Fin k) :
    (existsShift w r s a b c d C).rename ρ = existsShift (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ C) := by
  simp only [existsShift, Formula.rename, tail_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_tail {m} {Γ : Context m} (w r s a b c d C R S : Fin m)
    (hh : Derives Γ (state w r s a b c d C R S)) : Derives Γ (tail w r s a b c d C R) := by
  apply Derives.exI S
  exact of_eq (by simp only [Formula.instantiate, state_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem intro_exists {m} {Γ : Context m} (w r s a b c d C R S : Fin m)
    (hh : Derives Γ (state w r s a b c d C R S)) : Derives Γ (existsShift w r s a b c d C) := by
  apply Derives.exI R
  exact of_eq (by simp only [Formula.instantiate, tail_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (intro_tail w r s a b c d C R S hh)

theorem exists_shift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d C : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTermImageSyntax.maps w r s a b c d))
    (hC : Derives Γ (successor C c)) :
    Derives Γ (existsShift w r s a b c d C) := by
  have hcd := SyntaxTermImageSyntax.target_contexts w r s a b c d hi
  let R := SyntaxFreeShiftSyntax.shiftMap w.castSucc c.castSucc C.castSucc (Fin.last m)
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxFreeShiftGraph.exists_map hZ w c C hw (.conjL hcd) hC)
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw R)
  let S := SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add S (Context.image Formula.raise Ξ)
  apply Derives.exE (p := S) (SyntaxIdentityGraph.exists_map (ZFContext.under hZ R) w.castSucc d.castSucc (under (.conjR hcd) R))
  have hZ2 := ZFContext.under (ZFContext.under hZ R) S
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 S)
  have hi2 : Derives Δ (SyntaxTermImageSyntax.maps w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.maps_rename]) (under (under hi R) S)
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hr2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc c.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [R, Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (under hR S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hm : Derives Δ (SyntaxIndexMapSyntax.maps w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc) := .conjI (.conjL (.conjR hr2)) (.conjL hS)
  have he := SyntaxTermImagePushBoth.exists_both hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc hw2 hm hi2
  have ho := intro_exists w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjI hr2 (.conjI hS he))
  exact of_eq (by simp only [Formula.raise, existsShift_rename]) ho

end PPAC.Migration.Internal.SyntaxTermImageBoundShift
