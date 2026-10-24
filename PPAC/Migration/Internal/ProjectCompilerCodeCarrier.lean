import PPAC.Migration.Internal.ProjectCompilerCodeTransport

/-! Actual compiler set recursion or guarded output relation; output correctness and functionality remain unproved. -/
namespace PPAC.Migration.Internal.ProjectCompilerCodeCarrier
open Source SourceAlgebra SourceLogic PowerSetSyntax ProjectCompilerJudgmentSyntax ProjectCompilerCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c d t : Fin m)
    (hc : Derives Γ (carrier w a c)) (ht : Derives Γ (carrier w d t)) :
    Derives Γ ((Formula.equal a d).conj (.equal c t)) := by
  have he := (ZFContext.arithmetic hZ).base.extensionality
  have ha := PowerSetLogic.unique a d w he (.conjL hc) (.conjL ht)
  have ht' := PowerSetLogic.subst_base t d a (eq_symm ha) (.conjR ht)
  exact .conjI ha (PowerSetLogic.unique c t a he (.conjR hc) ht')

theorem exists_carrier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) : Derives Γ (existsCarrier w) := by
  have hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0) :=
    .hyp (hZ _ ⟨_, Source.SetLanguage.IsZFAxiom.powerSet, rfl⟩)
  have heA := power_instance w hp
  let A := powerOf (Fin.last m) w.castSucc
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  apply Derives.exE (p := A) heA
  have hp1 : Derives Ξ (Source.SetLanguage.powerSet.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp A
  have heC := power_instance (Fin.last m) hp1
  let C := powerOf (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply Derives.exE (p := C) heC
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hA2 : Derives Δ (powerOf (Fin.last m).castSucc w.castSucc.castSucc) := by
    simpa only [A, Formula.raise, powerOf_rename] using under hA C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout : Derives Δ (existsCarrier w.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc
    apply Derives.exI (Fin.last (m+1))
    simp only [Formula.instantiate, carrier_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hA2 hC
  simpa only [Formula.raise, existsCarrier_rename] using hout

theorem atCarrier_of_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n b f : Fin m)
    (hc : Derives Γ (carrier w a c)) (ht : Derives Γ (compiled w n b f)) : Derives Γ (atCarrier w c n b f) := by
  let B := body w n b f
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_code w n b f _ ht
  have hc2 : Derives Δ (carrier w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, carrier_rename] using OrderedPairElimination.under_two hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := unique (ZFContext.under_two hZ B) _ _ _ _ _ (.conjL hB) hc2
  have hout := ProjectCompilerCodeTransport.atCarrier_carrier _ _ _ _ _ _ (.conjR he) (.conjR hB)
  simpa only [Formula.raise, atCarrier_rename] using hout

theorem code_iff_atCarrier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n b f : Fin m)
    (hc : Derives Γ (carrier w a c)) : Derives Γ ((compiled w n b f).iff (atCarrier w c n b f)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact atCarrier_of_code (ZFContext.add hZ _) w a c n b f (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_code w a c n b f (add hc _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.ProjectCompilerCodeCarrier
