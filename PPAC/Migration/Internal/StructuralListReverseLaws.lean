import PPAC.Migration.Internal.StructuralReverseFieldAtMirror

/-! Actual reverse fields obey the exact reflected-index equation; reversal is symmetric and involutive internally. -/
namespace PPAC.Migration.Internal.StructuralListReverseLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListReverseSyntax StructuralReverseIndexSyntax
open StructuralListFieldSyntax (field field_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem field_at_mirror {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l r i j y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (reading w n l r)) (hm : Derives Γ (mirror w l i j)) :
    Derives Γ ((field w r i y).iff (field w n j y)) := by
  have hA := reading_at w n l r i y hr (StructuralReverseIndexArithmetic.input_bound hZ w l i j hw hm)
  have hB := StructuralReverseFieldAtMirror.at_mirror hZ w n l i j y hw hm
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hB) _) (.impE (add (.conjL hA) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hA) _) (.impE (add (.conjR hB) _) (.hyp (Or.inl rfl)))

theorem symmetric_reading {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l r : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hr : Derives Γ (reading w n l r)) : Derives Γ (reading w r l n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (slot 2 0) (old 2 l)
  let Δ := Context.add H (raisedContext 2 Γ)
  have hZ2 := ZFContext.add (HornBinderRules.zf_many 2 hZ) H
  have hw2 := of_eq (omega_rename w (old 2)) (add (HornBinderRules.under_many 2 hw) H)
  have hl2 : Derives Δ (.mem (old 2 l) (old 2 w)) := add (HornBinderRules.under_many 2 hl) H
  have hr2 := of_eq (reading_rename w n l r (old 2)) (add (HornBinderRules.under_many 2 hr) H)
  let R := mirror (old 2 w).castSucc (old 2 l).castSucc (slot 2 0).castSucc (Fin.last (m+2))
  let Ξ := Context.add R (Context.image Formula.raise Δ)
  apply Derives.exE (p := R) (StructuralReverseIndexExistence.exists_partner hZ2 (old 2 w) (old 2 l) (slot 2 0) hw2 hl2 (.hyp (Or.inl rfl)))
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 R
  have hw3 := of_eq (omega_rename (old 2 w) Fin.castSucc) (under hw2 R)
  have hr3 := of_eq (reading_rename (old 2 w) (old 2 n) (old 2 l) (old 2 r) Fin.castSucc) (under hr2 R)
  have hSym := StructuralReverseIndexArithmetic.symmetric hZ3 _ _ _ _ hw3 hR
  have hField := field_at_mirror hZ3 (old 2 w).castSucc (old 2 n).castSucc (old 2 l).castSucc (old 2 r).castSucc (Fin.last (m+2)) (slot 2 0).castSucc (slot 2 1).castSucc hw3 hr3 hSym
  have hValue := StructuralReverseFieldAtMirror.at_mirror hZ3 (old 2 w).castSucc (old 2 r).castSucc (old 2 l).castSucc (slot 2 0).castSucc (Fin.last (m+2)) (slot 2 1).castSucc hw3 hR
  have hout : Derives Ξ ((field (old 2 w).castSucc (old 2 n).castSucc (slot 2 0).castSucc (slot 2 1).castSucc).iff
      (StructuralReverseFieldSyntax.value (old 2 w).castSucc (old 2 r).castSucc (old 2 l).castSucc (slot 2 0).castSucc (slot 2 1).castSucc)) := by
    apply Derives.conjI
    · apply Derives.impI
      exact .impE (add (.conjR hValue) _) (.impE (add (.conjR hField) _) (.hyp (Or.inl rfl)))
    · apply Derives.impI
      exact .impE (add (.conjL hField) _) (.impE (add (.conjL hValue) _) (.hyp (Or.inl rfl)))
  have hs0 : slot (m := m) 2 0 = (Fin.last m).castSucc := by
    change (Fin.lastCases (Fin.last (m+1)) (fun j : Fin 1 => (slot (m := m) 1 j).castSucc) (0 : Fin 1).castSucc) = (Fin.last m).castSucc
    rw [Fin.lastCases_castSucc]
    change ((Fin.lastCases (Fin.last m) (fun j : Fin 0 => (slot (m := m) 0 j).castSucc) (Fin.last 0)) : Fin (m+1)).castSucc = (Fin.last m).castSucc
    rw [Fin.lastCases_last]
  have hs1 : slot (m := m) 2 1 = Fin.last (m+1) := by
    change Fin.lastCases (Fin.last (m+1)) (fun j : Fin 1 => (slot (m := m) 1 j).castSucc) (Fin.last 1) = Fin.last (m+1)
    exact Fin.lastCases_last
  simpa only [Formula.raise,Formula.rename,Formula.iff,field_rename,StructuralReverseFieldSyntax.value_rename,hs0,hs1,old] using hout

theorem symmetric_at_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (atLength w n l r)) : Derives Γ (atLength w r l n) :=
  .conjI (.conjL (.conjR hr)) (.conjI (.conjL hr)
    (symmetric_reading hZ w n l r hw (StructuralListLengthBasic.length_member _ _ _ (.conjL hr)) (.conjR (.conjR hr))))

theorem symmetric {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (reverses w n r)) : Derives Γ (reverses w r n) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (atLength w.castSucc n.castSucc (Fin.last m) r.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hs := symmetric_at_length (ZFContext.under hZ R) _ _ _ _ hw1 (.conjR hR)
  simpa only [Formula.raise,reverses_rename] using intro_reverse _ _ _ _ (.conjL hR) hs

theorem involutive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (reverses w n r)) (hs : Derives Γ (reverses w r s)) : Derives Γ (.equal s n) :=
  StructuralListReverseUnique.unique hZ w r s n hw hs (symmetric hZ w n r hw hr)

end PPAC.Migration.Internal.StructuralListReverseLaws
