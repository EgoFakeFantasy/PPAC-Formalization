import PPAC.Migration.Internal.StrictLookupSink

/-! 原对象ω归纳关闭全部内部执行索引的空集吸收不变量。 -/
namespace PPAC.Migration.Internal.StrictLookupSinkInduction
open Source SourceAlgebra SourceLogic OmegaSyntax StrictLookupSink
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem base {m} {Γ : Context m} (ρ : Fin 2 → Fin m) : Derives Γ (OmegaInductionSyntax.base StrictLookupSink.matrix ρ) := by
  simp only [OmegaInductionSyntax.base, StrictLookupSink.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  exact StrictLookupSink.empty_property _ _ _ (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (OmegaInductionSyntax.step StrictLookupSink.matrix ρ (ρ 0)) := by
  simp only [OmegaInductionSyntax.step, StrictLookupSink.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc (ρ 0).castSucc.castSucc
  let I := property (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (Fin.last m).castSucc
  let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ := Context.add S (Context.add I (Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) M) I) S
  have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)) M) I) S
  exact StrictLookupSink.property_successor hZ2 _ _ _ _ hw2
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (.all ((Formula.mem (Fin.last m) (ρ 0).castSucc).imp (property (ρ 0).castSucc (ρ 1).castSucc (Fin.last m)))) := by
  have h := OmegaInduction.induction_on_omega StrictLookupSink.matrix ρ (ρ 0)
    (ZFContext.separation hZ StrictLookupSink.matrix) hw (base ρ) (step hZ ρ hw)
  simpa only [OmegaInductionSyntax.holds, StrictLookupSink.matrix_pred, paramsUp] using h

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) : Derives Γ (property w n r) := by
  have hall := all_properties hZ (Source.SetLanguage.args2 w n) (by simpa only [PairSyntax.args2_first] using hw)
  have h : Derives Γ ((Formula.mem r w).imp (property w n r)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, PairSyntax.args2_first, PairSyntax.args2_second, id_eq] using Derives.allE r hall
  exact .impE h hr
theorem empty_iteration {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w))
    (hn : Derives Γ (empty n)) (hy : Derives Γ (StructuralListProjectionSyntax.iteration false w n i y)) : Derives Γ (empty y) :=
  StrictLookupSink.at_value w n i y (at_index hZ w n i hw hi) hn hy

end PPAC.Migration.Internal.StrictLookupSinkInduction
