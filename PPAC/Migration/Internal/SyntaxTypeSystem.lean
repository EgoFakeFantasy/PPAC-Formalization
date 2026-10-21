import PPAC.Migration.Internal.SyntaxTypeSystemSyntax

/-! 在原ZF内实际取得ω、三层载体、完整状态递归和全内部11构造定律；无额外存在前提。 -/
namespace PPAC.Migration.Internal.SyntaxTypeSystem
open Source SourceAlgebra SourceLogic OmegaSyntax PowerSetSyntax SyntaxContextCarrierSyntax SyntaxTypeRecursionSyntax SyntaxTypeSystemSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (powerOf a w)) (hc : Derives Γ (powerOf c a)) :
    Derives Γ (universalLaw w c) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ3 := ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by
    simpa only [omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw))
  have ha3 : Derives Δ (powerOf a.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc) := by
    simpa only [powerOf_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha))
  have hc3 : Derives Δ (powerOf c.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc) := by
    simpa only [powerOf_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc))
  exact SyntaxTypeRecursive.recursive_iff hZ3 w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 ha3 hc3

theorem actual_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (system w) := by
  have he := SyntaxContextCarrier.exists_tower hZ w
  let T := tower w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
  let Δ := Context.add T (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  have hZ3 := SyntaxAtomLogic.zf_under_three hZ T
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using SyntaxAtomLogic.under_three hw T
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hr := SyntaxTypeRecursors.all_unique hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc
  have hl := all_law hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
    hw3 (.conjL hT) (.conjL (.conjR hT))
  have hout : Derives Δ (system w.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc.castSucc
    apply Derives.exI (Fin.last (m+1)).castSucc
    apply Derives.exI (Fin.last (m+2))
    simp only [systemBody, Formula.instantiate, Formula.rename, tower_rename, recursors_rename, universalLaw_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hT (.conjI hr hl)
  have hh : Derives Δ (system w).raise.raise.raise := by
    simpa only [Formula.raise, system_rename] using hout
  refine Derives.weaken ?_ hh
  rintro q (hq | ⟨s, ⟨t, ht, h1⟩, h2⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ht, h1⟩, h2⟩

theorem existence {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) :
    Derives Γ (existsSystem.rename Fin.elim0) := by
  have he := ZFContext.closed hZ ObjectOmega.source_ZF_existence
  let W := omega (Fin.last m)
  let Δ := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at he
  apply Derives.exE (p := W) he
  have hW : Derives Δ W := .hyp (Or.inl rfl)
  have hs := actual_system (ZFContext.under hZ W) (Fin.last m) hW
  have hout : Derives Δ (existsSystem.rename Fin.elim0) := by
    simp only [existsSystem, Formula.rename, omega_rename, system_rename, Formula.liftRen, Fin.lastCases_last]
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, omega_rename, system_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hW hs
  simpa only [Formula.raise, closed_rename] using hout
end PPAC.Migration.Internal.SyntaxTypeSystem
