import PPAC.Migration.Internal.SyntaxMixedFormulaStateExistence

/-! 混合历史读取真实七字段状态；量词使用真实数值binder同时更新两份环境码。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaQuerySyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxMixedFormulaStateSyntax
open SyntaxRenameQuerySyntax (of_eq)

def contains {m} (w v r s a b c d q : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) v.castSucc).conj
    (state w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m)))

def read {m} (w h x r s a b c d q : Fin m) : Formula m := .ex
  ((edge h.castSucc x.castSucc (Fin.last m)).conj
    (contains w.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc))

def advancedBody {m} (w h x r s a b c d q : Fin m) : Formula (m+4) :=
  (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))).conj
  (read w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
    (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc)

def advanced {m} (w h x r s a b c d q : Fin m) : Formula m := .ex (.ex (.ex (.ex (advancedBody w h x r s a b c d q))))

theorem contains_rename {m k} (w v r s a b c d q : Fin m) (ρ : Fin m → Fin k) :
    (contains w v r s a b c d q).rename ρ = contains (ρ w) (ρ v) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [contains, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem read_rename {m k} (w h x r s a b c d q : Fin m) (ρ : Fin m → Fin k) :
    (read w h x r s a b c d q).rename ρ = read (ρ w) (ρ h) (ρ x) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [read, Formula.rename, edge_rename, contains_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem advanced_rename {m k} (w h x r s a b c d q : Fin m) (ρ : Fin m → Fin k) :
    (advanced w h x r s a b c d q).rename ρ = advanced (ρ w) (ρ h) (ρ x) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [advanced, advancedBody, Formula.rename, SyntaxCodedMixedBinderSyntax.lifted_rename, read_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_contains {m} {Γ : Context m} (w v r s a b c d q t : Fin m)
    (ht : Derives Γ (.mem t v)) (hs : Derives Γ (state w r s a b c d q t)) : Derives Γ (contains w v r s a b c d q) := by
  apply Derives.exI t
  simp only [Formula.instantiate, Formula.rename, state_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ht hs

theorem intro_read {m} {Γ : Context m} (w h x r s a b c d q v : Fin m)
    (hv : Derives Γ (edge h x v)) (hc : Derives Γ (contains w v r s a b c d q)) : Derives Γ (read w h x r s a b c d q) := by
  apply Derives.exI v
  simp only [Formula.instantiate, Formula.rename, edge_rename, contains_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hv hc

theorem intro_advanced {m} {Γ : Context m} (w h x r s a b c d q A C K H : Fin m)
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H))
    (hr : Derives Γ (read w h x K H A b C d q)) : Derives Γ (advanced w h x r s a b c d q) := by
  apply Derives.exI A
  apply Derives.exI C
  apply Derives.exI K
  apply Derives.exI H
  simp only [advancedBody, Formula.instantiate, Formula.rename, SyntaxCodedMixedBinderSyntax.lifted_rename, read_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hl hr

theorem eliminate_advanced {m} {Γ : Context m} (w h x r s a b c d q : Fin m) (P : Formula m)
    (he : Derives Γ (advanced w h x r s a b c d q))
    (hc : Derives (Context.add (advancedBody w h x r s a b c d q)
      (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))
      P.raise.raise.raise.raise) : Derives Γ P := SyntaxRenameBinders.eliminate_4 (advancedBody w h x r s a b c d q) P he hc

theorem contains_subst_set {m} {Γ : Context m} (w v t r s a b c d q : Fin m)
    (he : Derives Γ (.equal v t)) (hc : Derives Γ (contains w v r s a b c d q)) : Derives Γ (contains w t r s a b c d q) := by
  let P := contains w.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc
  have ev : P.instantiate v = contains w v r s a b c d q := by
    simp only [P, Formula.instantiate, contains_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have et : P.instantiate t = contains w t r s a b c d q := by
    simp only [P, Formula.instantiate, contains_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq et (Derives.eqSubst P he (of_eq ev.symm hc))
end PPAC.Migration.Internal.SyntaxMixedFormulaQuerySyntax
