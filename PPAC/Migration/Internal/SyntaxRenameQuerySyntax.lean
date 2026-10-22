import PPAC.Migration.Internal.ObjectSyntaxMapCodeState

/-! 重命名历史读取真实状态集合值和原七字段状态码；量词真实提升bound自然码，free码不变。 -/
namespace PPAC.Migration.Internal.SyntaxRenameQuerySyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameStateSyntax SyntaxMapLiftSyntax

def contains {m} (w v r s a b c d q : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) v.castSucc).conj
    (state w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m)))

def read {m} (w h x r s a b c d q : Fin m) : Formula m := .ex
  ((edge h.castSucc x.castSucc (Fin.last m)).conj
    (contains w.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc))

def advancedBody {m} (w h x r s a b c d q : Fin m) : Formula (m+3) :=
  (codedLift w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).conj
  (read w.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc (Fin.last (m+2))
    s.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc
    d.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc)

def advanced {m} (w h x r s a b c d q : Fin m) : Formula m := .ex (.ex (.ex (advancedBody w h x r s a b c d q)))

theorem of_eq {m} {Γ : Context m} {p q : Formula m} (he : p = q) (hp : Derives Γ p) : Derives Γ q := he ▸ hp

theorem contains_rename {m k} (w v r s a b c d q : Fin m) (ρ : Fin m → Fin k) :
    (contains w v r s a b c d q).rename ρ = contains (ρ w) (ρ v) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [contains, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem read_rename {m k} (w h x r s a b c d q : Fin m) (ρ : Fin m → Fin k) :
    (read w h x r s a b c d q).rename ρ = read (ρ w) (ρ h) (ρ x) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [read, Formula.rename, edge_rename, contains_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem advanced_rename {m k} (w h x r s a b c d q : Fin m) (ρ : Fin m → Fin k) :
    (advanced w h x r s a b c d q).rename ρ = advanced (ρ w) (ρ h) (ρ x) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [advanced, advancedBody, Formula.rename, codedLift_rename, read_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

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

theorem intro_advanced {m} {Γ : Context m} (w h x r s a b c d q u v l : Fin m)
    (hl : Derives Γ (codedLift w a c r u v l)) (hr : Derives Γ (read w h x l s u b v d q)) :
    Derives Γ (advanced w h x r s a b c d q) := by
  apply Derives.exI u
  apply Derives.exI v
  apply Derives.exI l
  simp only [advancedBody, Formula.instantiate, Formula.rename, codedLift_rename, read_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hl hr

theorem eliminate_advanced {m} {Γ : Context m} (w h x r s a b c d q : Fin m) (P : Formula m)
    (he : Derives Γ (advanced w h x r s a b c d q))
    (hc : Derives (Context.add (advancedBody w h x r s a b c d q)
      (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) P.raise.raise.raise) : Derives Γ P := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨s1, ⟨s2, hs, h2⟩, h1⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨s1, Or.inr ⟨s2, Or.inr hs, h2⟩, h1⟩

theorem contains_subst_set {m} {Γ : Context m} (w v t r s a b c d q : Fin m)
    (he : Derives Γ (.equal v t)) (hc : Derives Γ (contains w v r s a b c d q)) : Derives Γ (contains w t r s a b c d q) := by
  let P := contains w.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc
  have ev : P.instantiate v = contains w v r s a b c d q := by
    simp only [P, Formula.instantiate, contains_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have et : P.instantiate t = contains w t r s a b c d q := by
    simp only [P, Formula.instantiate, contains_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq et (Derives.eqSubst P he (of_eq ev.symm hc))
end PPAC.Migration.Internal.SyntaxRenameQuerySyntax
