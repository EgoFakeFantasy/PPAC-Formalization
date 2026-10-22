import PPAC.Migration.Internal.SyntaxIndexLiftTerms

/-! 只给原完整索引图时，实际联合取得两个后继作用域及唯一完整提升图。 -/
namespace PPAC.Migration.Internal.SyntaxIndexLiftSystem
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxIndexMapSyntax SyntaxIndexLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def system {m} (w r a c : Fin m) : Formula m := .ex (.ex
  (liftFiber w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1))))

theorem system_rename {m n} (w r a c : Fin m) (ρ : Fin m → Fin n) :
    (system w r a c).rename ρ = system (ρ w) (ρ r) (ρ a) (ρ c) := by
  simp only [system, Formula.rename, liftFiber_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem actual_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c)) : Derives Γ (system w r a c) := by
  have he := InsertExistence.exists_insert a a (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let U := successor (Fin.last m) a.castSucc
  let Ξ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at he
  apply Derives.exE he
  have hZ1 := ZFContext.under hZ U
  have hv := InsertExistence.exists_insert c.castSucc c.castSucc (ZFContext.arithmetic hZ1).base.pairing (ZFContext.arithmetic hZ1).base.union
  let V := successor (Fin.last (m+1)) c.castSucc.castSucc
  let Δ := Context.add V (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex V) at hv
  apply Derives.exE hv
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw U) V
  have hm2 : Derives Δ (indexMap w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, indexMap_rename] using under (under hm U) V
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hu2 : Derives Δ (successor (Fin.last m).castSucc a.castSucc.castSucc) := by
    simpa only [U, Formula.raise, successor_rename] using under hU V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hf := SyntaxIndexLift.actual_fiber (ZFContext.under hZ1 V) w.castSucc.castSucc r.castSucc.castSucc
    a.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hm2 hu2 hV
  have ho : Derives Δ (system w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, Formula.rename, liftFiber_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf
  simpa only [Formula.raise, system_rename] using ho
end PPAC.Migration.Internal.SyntaxIndexLiftSystem
