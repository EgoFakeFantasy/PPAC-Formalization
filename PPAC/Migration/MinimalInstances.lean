import PPAC.Migration.MinimalLogic
import PPAC.Migration.SeparationSyntax

/-! 极小元证明只实例化一个分离实例与原始正则公理。 -/
namespace PPAC.Migration.MinimalInstances
open Source SourceAlgebra MinimalPredicates
open ReplacementPredicates (paramsUp)

theorem foundation_core : Source.SetLanguage.foundation =
    .all ((inhabited (Fin.last 0)).imp (regular (Fin.last 0))) := rfl

theorem separation_core {n} (p : Formula (n+1)) : SeparationSyntax.core p =
    .all (separationExists p Fin.castSucc (Fin.last n)) := rfl

theorem foundation_instance {m} {Γ : Context m} (c : Fin m)
    (h : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0)) :
    Derives Γ ((inhabited c).imp (regular c)) := by
  rw [foundation_core] at h
  have hi := Derives.allE c h
  simpa only [Formula.rename, Formula.instantiate, inhabited_rename, regular_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem separation_instance {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (a : Fin m) (h : Derives Γ ((Source.SetLanguage.separation p).rename Fin.elim0)) :
    Derives Γ (separationExists p ρ a) := by
  rw [SeparationSyntax.source_core] at h
  have hs := specialize_close (SeparationSyntax.core p) ρ h
  rw [separation_core] at hs
  have hi := Derives.allE a hs
  simpa only [Formula.rename, Formula.instantiate, separationExists_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.MinimalInstances
