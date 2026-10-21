import PPAC.Migration.LayerRankSyntax

/-! 已证最小序数模式和任意内部序数族严格界的对象实例。 -/
namespace PPAC.Migration.LayerCoverClosedInstances
open Source SourceAlgebra SourceLogic OrdinalSyntax LayerCoverSyntax LayerRankSyntax

theorem rank_fiber {m} {Γ : Context m} (x : Fin m)
    (hc : Derives Γ ((ObjectOrdinalLeast.uniquenessSentence containsMatrix).rename Fin.elim0))
    (hx : Derives Γ (cover x)) : Derives Γ (fiber x) := by
  have hi := specialize_close ((OrdinalLeastSyntax.has containsMatrix (id : Fin 1 → Fin 1)).imp
    (OrdinalLeastSyntax.fiber containsMatrix id)) (fun _ => x) hc
  have h : Derives Γ ((cover x).imp (fiber x)) := by
    simpa only [Formula.rename, OrdinalLeastSyntax.has_rename, OrdinalLeastSyntax.fiber_rename,
      id_eq, contains_has, least_fiber] using hi
  exact .impE h hx

theorem strict_bound {m} {Γ : Context m} (c : Fin m)
    (hc : Derives Γ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0))
    (ho : Derives Γ (OrdinalFamilySyntax.ordinals c)) : Derives Γ (OrdinalStrictBound.boundExists c) := by
  have hi := specialize_close ((OrdinalFamilySyntax.ordinals (0 : Fin 1)).imp (OrdinalStrictBound.boundExists 0)) (fun _ => c) hc
  have h : Derives Γ ((OrdinalFamilySyntax.ordinals c).imp (OrdinalStrictBound.boundExists c)) := by
    simpa only [Formula.rename, OrdinalFamilySyntax.ordinals_rename, OrdinalStrictBound.boundExists_rename] using hi
  exact .impE h ho

theorem strict_at {m} {Γ : Context m} (c a b : Fin m) (hh : Derives Γ (OrdinalStrictBound.strictUpper c a)) :
    Derives Γ ((Formula.mem b c).imp (.mem b a)) := by
  have hi := Derives.allE b hh
  simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.LayerCoverClosedInstances
