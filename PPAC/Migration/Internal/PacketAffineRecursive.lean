import PPAC.Migration.Internal.PacketAffineStep

/-! Complete affine recursive equation on all internal digit, tail and output candidates. -/
namespace PPAC.Migration.Internal.PacketAffineRecursive
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketAffineSyntax PacketAffineCore
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem natural_split {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w t : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) : Derives Γ (OmegaStructureSyntax.split w t) := by
  have ha := Derives.allE t (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw)
  have hi : Derives Γ ((Formula.mem t w).imp (OmegaStructureSyntax.split w t)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, OmegaStructureSyntax.split_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ha
  exact .impE hi ht

theorem step_case_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d t n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (stepCase w B d t n)) : Derives Γ (affine w B d t n) := by
  let P := stepBody w B d t n
  let Δ := Context.add P (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 P _ hc
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw P)
  have ho := PacketAffineStep.advance (HornBinderRules.zf_body 2 hZ P)
    (old 2 w) (old 2 B) (old 2 d) (slot 2 0) (slot 2 1) (old 2 t) (old 2 n)
    hw2 (.conjL (.conjR hP)) (.conjL hP) (.conjR (.conjR hP))
  exact of_eq (affine_rename w B d t n (old 2)).symm ho

theorem recursive_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d t n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) :
    Derives Γ ((affine w B d t n).iff (criterion w B d t n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let A := affine w B d t n
    let ΓA := Context.add A Γ
    have hA : Derives ΓA A := .hyp (Or.inl rfl)
    have hsp := natural_split (ZFContext.add hZ A) w t (add hw A) (tail_guard w B d t n hA)
    apply Derives.disjE hsp
    · let Z := empty t
      have hz : Derives (Context.add Z ΓA) Z := .hyp (Or.inl rfl)
      have hv := Derives.impE (.conjL (PacketAffineZero.zero_iff (ZFContext.add (ZFContext.add hZ A) Z) w B d t n
        (add (add hw A) Z) (add (add hB A) Z) hz)) (add hA Z)
      exact .disjL (.conjI hz hv)
    · let Q := OmegaStructureSyntax.predecessor w t
      let P := (Formula.mem (Fin.last m) w.castSucc).conj (successor t.castSucc (Fin.last m))
      let Δ := Context.add P (Context.image Formula.raise (Context.add Q ΓA))
      apply Derives.exE (p := P) (.hyp (Or.inl rfl))
      have hP : Derives Δ P := .hyp (Or.inl rfl)
      have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add (add hw A) Q) P)
      have hA1 := of_eq (affine_rename w B d t n Fin.castSucc) (under (add hA Q) P)
      have hs := PacketAffineStep.retreat (ZFContext.under (ZFContext.add (ZFContext.add hZ A) Q) P)
        w.castSucc B.castSucc d.castSucc (Fin.last m) t.castSucc n.castSucc hw1 (.conjL hP) (.conjR hP) hA1
      have ho : Derives Δ (criterion w.castSucc B.castSucc d.castSucc t.castSucc n.castSucc) := .disjR hs
      exact of_eq (criterion_rename w B d t n Fin.castSucc).symm ho
  · apply Derives.impI
    let C := criterion w B d t n
    let ΓC := Context.add C Γ
    apply Derives.disjE (Derives.hyp (Γ := ΓC) (Or.inl rfl))
    · let Z := (empty t).conj ((Formula.mem d B).conj (.equal n d))
      have hz : Derives (Context.add Z ΓC) Z := .hyp (Or.inl rfl)
      exact .impE (.conjR (PacketAffineZero.zero_iff (ZFContext.add (ZFContext.add hZ C) Z) w B d t n
        (add (add hw C) Z) (add (add hB C) Z) (.conjL hz))) (.conjR hz)
    · exact step_case_forward (ZFContext.add (ZFContext.add hZ C) _) w B d t n (add (add hw C) _) (.hyp (Or.inl rfl))

def lawBody {m} (w B : Fin m) : Formula (m+3) :=
  (affine (old 3 w) (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2)).iff
    (criterion (old 3 w) (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2))

def universalLaw {m} (w B : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (lawBody w B)

theorem lawBody_lift {m j} (w B : Fin m) (σ : Fin m → Fin j) :
    (lawBody w B).rename (lift 3 σ) = lawBody (σ w) (σ B) := by
  simp only [lawBody, Formula.iff, Formula.rename, affine_rename, criterion_rename, lift_old, lift_slot]

theorem universalLaw_rename {m j} (w B : Fin m) (σ : Fin m → Fin j) :
    (universalLaw w B).rename σ = universalLaw (σ w) (σ B) := by
  simp only [universalLaw, OriginalUniversalBlock.allMany_rename, lawBody_lift]

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) : Derives Γ (universalLaw w B) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  have hB3 : Derives (raisedContext 3 Γ) (.mem (old 3 B) (old 3 w)) := HornBinderRules.under_many 3 hB
  exact recursive_iff (HornBinderRules.zf_many 3 hZ) (old 3 w) (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hB3

end PPAC.Migration.Internal.PacketAffineRecursive
