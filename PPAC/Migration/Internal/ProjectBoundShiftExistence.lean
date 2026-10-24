import PPAC.Migration.Internal.ProjectBoundShiftLaws

/-! Actual successors and shifted term codes are constructed and object-eliminated. -/
namespace PPAC.Migration.Internal.ProjectBoundShiftExistence
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectBoundShiftSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i x : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxVariableSyntax.code true w i x)) : Derives Γ (existsOutput w x) := by
  have hi := SyntaxVariableDecode.index_natural true w i x hc
  let J := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) i.castSucc)
  let Δ := Context.add J (Context.image Formula.raise Γ)
  apply Derives.exE (p := J) (Derives.impE (OmegaSyntax.step_at w i (.conjL hw)) hi)
  have hZ1 := ZFContext.under hZ J
  have hJ : Derives Δ J := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw J)
  have hc1 := of_eq (SyntaxVariableSyntax.code_rename true w i x Fin.castSucc) (under hc J)
  let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (SyntaxVariableSyntax.code true w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add Y (Context.image Formula.raise Δ)
  apply Derives.exE (p := Y) (SyntaxVariables.exists_code hZ1 true w.castSucc (Fin.last m) hw1 (.conjL hJ))
  have hJ2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (successor (Fin.last m).castSucc i.castSucc.castSucc)) :=
    of_eq (by simp only [J, Formula.raise, Formula.rename, successor_rename]) (under hJ Y)
  have hc2 := of_eq (SyntaxVariableSyntax.code_rename true w.castSucc i.castSucc x.castSucc Fin.castSucc) (under hc1 Y)
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hs := intro_shifted w.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1)) i.castSucc.castSucc (Fin.last m).castSucc
    (.conjI hc2 (.conjI (.conjR hJ2) (.conjR hY)))
  have ho := intro_exists w.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1)) (.conjL hY) hs
  exact of_eq (by simp only [Formula.raise, existsOutput_rename]) ho

theorem exists_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b x : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (SyntaxTermSyntax.branch true w b x)) : Derives Γ (existsOutput w x) := by
  let I := SyntaxTermSyntax.branchWitness true w b x
  let Δ := Context.add I (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch true w b x _ hx
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw I)
  have ho := at_index (ZFContext.under hZ I) w.castSucc (Fin.last m) x.castSucc hw1 (.conjR hI)
  exact of_eq (existsOutput_rename w x Fin.castSucc).symm ho

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b x : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (SyntaxTermSyntax.branch true w b x)) : Derives Γ (fiber w x) := by
  let Y := (Formula.mem (Fin.last m) w.castSucc).conj (shifted w.castSucc x.castSucc (Fin.last m))
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) (exists_output hZ w b x hw hx)
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Y)
  have hu := ProjectBoundShiftLaws.unique_output (ZFContext.under hZ Y) w.castSucc x.castSucc (Fin.last m) hw1 (.conjR hY)
  have ho : Derives Δ (fiber w.castSucc x.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Y, Formula.instantiate, Formula.rename, shifted_rename, uniqueOutput_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hY hu)
  exact of_eq (fiber_rename w x Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProjectBoundShiftExistence
