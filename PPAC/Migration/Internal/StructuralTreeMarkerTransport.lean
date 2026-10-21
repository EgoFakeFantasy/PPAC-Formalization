import PPAC.Migration.Internal.StructuralTreeValiditySyntax

/-! 实际零/单位标志的对象等词传输；不同实际见证给相同接受/拒绝结果。 -/
namespace PPAC.Migration.Internal.StructuralTreeMarkerTransport
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralTreeEvaluationSyntax StructuralTreeRecursiveSyntax

theorem zero_subst {m} {Γ : Context m} (w z r e n y : Fin m) (heq : Derives Γ (.equal z r))
    (hy : Derives Γ (evaluation w z e n y)) : Derives Γ (evaluation w r e n y) := by
  have hi : Derives Γ ((evaluation w.castSucc (Fin.last m) e.castSucc n.castSucc y.castSucc).instantiate z) := by
    simpa only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (evaluation w.castSucc (Fin.last m) e.castSucc n.castSucc y.castSucc) heq hi
  simpa only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem unit_subst {m} {Γ : Context m} (w z e s n y : Fin m) (heq : Derives Γ (.equal e s))
    (hy : Derives Γ (evaluation w z e n y)) : Derives Γ (evaluation w z s n y) := by
  have hi : Derives Γ ((evaluation w.castSucc z.castSucc (Fin.last m) n.castSucc y.castSucc).instantiate e) := by
    simpa only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (evaluation w.castSucc z.castSucc (Fin.last m) n.castSucc y.castSucc) heq hi
  simpa only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem accepts_transport {m} {Γ : Context m} (w z e r s n : Fin m) (hz : Derives Γ (.equal z r)) (he : Derives Γ (.equal e s))
    (ha : Derives Γ (accepts w z e n)) : Derives Γ (accepts w r s n) :=
  output_subst w r s n e s he (unit_subst w r e s n e he (zero_subst w z r e n e hz ha))

theorem rejects_transport {m} {Γ : Context m} (w z e r s n : Fin m) (hz : Derives Γ (.equal z r)) (he : Derives Γ (.equal e s))
    (ha : Derives Γ (rejects w z e n)) : Derives Γ (rejects w r s n) :=
  output_subst w r s n z r hz (unit_subst w r e s n z he (zero_subst w z r e n z hz ha))
end PPAC.Migration.Internal.StructuralTreeMarkerTransport
