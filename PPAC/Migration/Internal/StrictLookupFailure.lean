import PPAC.Migration.Internal.StrictLookupSinkInduction

/-! 严格查表拒绝当前非法外壳和空列表；不会因默认零tail在后续恢复成功。 -/
namespace PPAC.Migration.Internal.StrictLookupFailure
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax StrictLookupSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem tail_has_head {m} {Γ : Context m} (w n : Fin m)
    (hc : Derives Γ (hasCons false w n)) : Derives Γ (hasCons true w n) := by
  let T := selected false w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) hc
  let B := StructuralListProjectionSyntax.body false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add B (Context.image Formula.raise Δ)
  apply Derives.exE (p := B) (.hyp (Or.inl rfl))
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hh := StructuralListProjectionSyntax.intro_selected true w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
    (.conjI (.conjI (.conjR (.conjL hB)) (.conjL (.conjL hB))) (.conjR hB))
  exact of_eq (by simp only [Formula.raise, hasCons_rename])
    (StructuralListProjectionSyntax.intro_hasCons true w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) hh)

theorem no_head_no_tail {m} {Γ : Context m} (w n : Fin m) (hn : Derives Γ (hasCons true w n).neg) :
    Derives Γ (hasCons false w n).neg := by
  apply Derives.impI
  exact .impE (add hn _) (tail_has_head w n (.hyp (Or.inl rfl)))

theorem successor_absurd {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hn : Derives Γ (hasCons true w n).neg) (hy : Derives Γ (returned w n s y)) : Derives Γ .bot := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) (.conjL (.conjL hw))
  have hZ1 := ZFContext.under hZ Z
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := of_eq (successor_rename s r Fin.castSucc) (under hs Z)
  have hy1 : Derives Δ (returned w.castSucc n.castSucc s.castSucc y.castSucc) := of_eq (returned_rename w n s y Fin.castSucc) (under hy Z)
  have hn1 : Derives Δ (hasCons true w.castSucc n.castSucc).neg := of_eq (by simp only [Formula.raise, Formula.neg, Formula.rename, hasCons_rename]) (under hn Z)
  have hZval : Derives Δ Z := .hyp (Or.inl rfl)
  have hStep : Derives Δ (step false w.castSucc n.castSucc (Fin.last m)) := .disjR (.conjI (no_head_no_tail w.castSucc n.castSucc hn1) (.conjR hZval))
  let T := body w.castSucc n.castSucc s.castSucc y.castSucc
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hy1
  have hZ2 := ZFContext.under hZ1 T
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 T)
  have hs2 : Derives Ξ (successor s.castSucc.castSucc r.castSucc.castSucc) := of_eq (successor_rename s.castSucc r.castSucc Fin.castSucc) (under hs1 T)
  have hr2 : Derives Ξ (.mem r.castSucc.castSucc w.castSucc.castSucc) := under (under hr Z) T
  have hz2 : Derives Ξ (empty (Fin.last m).castSucc) := of_eq (empty_rename (Fin.last m) Fin.castSucc) (under (.conjR hZval) T)
  have hStep2 : Derives Ξ (step false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := of_eq (step_rename false w.castSucc n.castSucc (Fin.last m) Fin.castSucc) (under hStep T)
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hTail := StructuralListShift.shift_forward hZ2 false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last (m+1)) hw2 hr2 hs2 hStep2 (.conjL hT)
  have hEmpty := StrictLookupSinkInduction.empty_iteration hZ2 w.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc (Fin.last (m+1)) hw2 hr2 hz2 hTail
  exact StrictLookupSink.selected_empty_absurd true w.castSucc.castSucc (Fin.last (m+1)) y.castSucc.castSucc hEmpty (.conjR hT)

theorem point_absurd {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w))
    (hn : Derives Γ (hasCons true w n).neg) (hy : Derives Γ (returned w n i y)) : Derives Γ .bot := by
  apply SourcePropositional.by_cases (empty i)
  · have hp := StrictLookupRules.zero_selected (ZFContext.add hZ _) w n i y (add hw _) (.hyp (Or.inl rfl))
    exact .impE (add hn _) (intro_hasCons true w n y (.impE (.conjL hp) (add hy _)))
  · let N := (empty i).neg
    let hd := OmegaStructureAlgebra.decomposition_at w i
      (OmegaStructureInduction.decomposition w (ZFContext.separation (ZFContext.add hZ N) OmegaStructureSyntax.splitMatrix) (add hw N)) (add hi N)
    have hp := OmegaStructureAlgebra.nonzero_predecessor w i hd (Derives.hyp (Γ := Context.add N Γ) (Or.inl rfl))
    let P := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise (Context.add N Γ))
    apply Derives.exE (p := P) hp
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw N) P)
    have hn1 : Derives Δ (hasCons true w.castSucc n.castSucc).neg := of_eq (by simp only [Formula.raise, Formula.neg, Formula.rename, hasCons_rename]) (under (add hn N) P)
    have hy1 : Derives Δ (returned w.castSucc n.castSucc i.castSucc y.castSucc) := of_eq (returned_rename w n i y Fin.castSucc) (under (add hy N) P)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    exact successor_absurd (ZFContext.under (ZFContext.add hZ N) P) w.castSucc n.castSucc (Fin.last m) i.castSucc y.castSucc hw1 (.conjL hP) (.conjR hP) hn1 hy1

theorem no_cons_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hn : Derives Γ (hasCons true w n).neg) :
    Derives Γ (rejected w n i) := by
  apply Derives.impI
  let C := hasOutput w n i
  let Y := returned w.castSucc n.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise (Context.add C Γ))
  apply Derives.exE (p := Y) (.hyp (Or.inl rfl))
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw C) Y)
  have hi1 : Derives Δ (.mem i.castSucc w.castSucc) := under (add hi C) Y
  have hn1 : Derives Δ (hasCons true w.castSucc n.castSucc).neg := of_eq (by simp only [Formula.raise, Formula.neg, Formula.rename, hasCons_rename]) (under (add hn C) Y)
  exact point_absurd (ZFContext.under (ZFContext.add hZ C) Y) w.castSucc n.castSucc i.castSucc (Fin.last m) hw1 hi1 hn1 (.hyp (Or.inl rfl))

theorem nil_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) :
    Derives Γ (rejected w n i) :=
  no_cons_rejected hZ w n i hw hi (StructuralListProjection.nil_no_cons hZ true w n hw hn)

theorem cons_zero_returns {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n z : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n)) (hz : Derives Γ (empty z)) :
    Derives Γ (returned w n z h) :=
  intro_returned w n z h n (StructuralListPositionLogic.zero_value hZ false w n z hw hz)
    (StructuralListProjection.selected_cons true w h t n hh ht hc)

end PPAC.Migration.Internal.StrictLookupFailure
