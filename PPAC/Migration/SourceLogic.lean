import PPAC.Migration.SourceAlgebra

/-! 仅由锁定19规则组成的源派生等词/新鲜变量接口。 -/
namespace PPAC.Migration.SourceLogic
open Source SourceAlgebra

theorem add {m} {Γ : Context m} {p : Formula m} (h : Derives Γ p) (q : Formula m) :
    Derives (Context.add q Γ) p := .weaken (fun _ hp => Or.inr hp) h

theorem under {m} {Γ : Context m} {p : Formula m} (h : Derives Γ p) (q : Formula (m+1)) :
    Derives (Context.add q (Context.image Formula.raise Γ)) p.raise :=
  .weaken (fun _ hp => Or.inr hp) (.rename Fin.castSucc h)

theorem eq_symm {m} {Γ : Context m} {s t : Fin m} (h : Derives Γ (.equal s t)) :
    Derives Γ (.equal t s) := by
  have hs : Derives Γ ((Formula.equal (Fin.last m) s.castSucc).instantiate s) := by
    simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      using (Derives.eqRefl (Γ := Γ) s)
  have hi := Derives.eqSubst (.equal (Fin.last m) s.castSucc) h hs
  simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem eq_trans {m} {Γ : Context m} {s t u : Fin m}
    (hst : Derives Γ (.equal s t)) (htu : Derives Γ (.equal t u)) : Derives Γ (.equal s u) := by
  have hs : Derives Γ ((Formula.equal s.castSucc (Fin.last m)).instantiate t) := by
    simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hst
  have hi := Derives.eqSubst (.equal s.castSucc (Fin.last m)) htu hs
  simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem mem_subst {m} {Γ : Context m} {s t w : Fin m}
    (hst : Derives Γ (.equal s t)) (hsw : Derives Γ (.mem s w)) : Derives Γ (.mem t w) := by
  have hs : Derives Γ ((Formula.mem (Fin.last m) w.castSucc).instantiate s) := by
    simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hsw
  have hi := Derives.eqSubst (.mem (Fin.last m) w.castSucc) hst hs
  simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.SourceLogic
