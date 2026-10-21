import PPAC.Migration.Internal.SequencePrefix

/-! 任意有限纯公式行测试的轨迹组合；非ZF/U专用检查器，不增加测试谓词公理。 -/
namespace PPAC.Migration.Internal.CheckedSequence
open Source SourceAlgebra SourceLogic GraphSyntax SequenceSyntax ReplacementPredicates

def rows {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (f : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (rel p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))))
def checked {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (f d b : Fin m) : Formula m :=
  (sequence f d b).conj (rows p ρ f)

theorem rows_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (f : Fin m) (r : Fin m → Fin k) :
    (rows p ρ f).rename r = rows p (fun i => r (ρ i)) (r f) := by
  simp only [rows, Formula.rename, edge_rename, rel_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem checked_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (f d b : Fin m) (r : Fin m → Fin k) :
    (checked p ρ f d b).rename r = checked p (fun i => r (ρ i)) (r f) (r d) (r b) := by
  simp only [checked, Formula.rename, sequence_rename, rows_rename]

theorem rows_at {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (f i y : Fin m)
    (hh : Derives Γ (rows p ρ f)) : Derives Γ ((edge f i y).imp (rel p ρ i y)) := by
  have hi := Derives.allE y (Derives.allE i hh)
  simpa only [Formula.instantiate, Formula.rename, edge_rename, rel_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem rel_subst_left {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x z y : Fin m)
    (he : Derives Γ (.equal x z)) (hp : Derives Γ (rel p ρ x y)) : Derives Γ (rel p ρ z y) := by
  have hi : Derives Γ ((rel p (paramsUp ρ) (Fin.last m) y.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, rel_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have hout := Derives.eqSubst (rel p (paramsUp ρ) (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, rel_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hout

theorem rel_subst_right {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x y z : Fin m)
    (he : Derives Γ (.equal y z)) (hp : Derives Γ (rel p ρ x y)) : Derives Γ (rel p ρ x z) := by
  have hi : Derives Γ ((rel p (paramsUp ρ) x.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, rel_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have hout := Derives.eqSubst (rel p (paramsUp ρ) x.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, rel_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hout

theorem appended_rows {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (g f d y : Fin m)
    (hf : Derives Γ (rows p ρ f)) (hy : Derives Γ (rel p ρ d y))
    (hl : Derives Γ (GraphInsertSyntax.edgeLaw g f d y)) : Derives Γ (rows p ρ g) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hf' : Derives Δ (rows p (paramsUp (paramsUp ρ)) f.castSucc.castSucc) := by
    simpa only [Formula.raise, rows_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hy' : Derives Δ (rel p (paramsUp (paramsUp ρ)) d.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, rel_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hy)
  have hl' : Derives Δ (GraphInsertSyntax.edgeLaw g.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, GraphInsertSyntax.edgeLaw_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hl)
  apply Derives.impI
  let E := edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  have hc := Derives.impE (.conjL (law_at g.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc y.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (add hl' E))) (.hyp (Or.inl rfl))
  apply Derives.disjE hc
  · exact .impE (add (add (rows_at p (paramsUp (paramsUp ρ)) f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hf') E) _) (.hyp (Or.inl rfl))
  · let B := (Formula.equal (Fin.last m).castSucc d.castSucc.castSucc).conj (.equal (Fin.last (m+1)) y.castSucc.castSucc)
    have hB : Derives (Context.add B (Context.add E Δ)) B := .hyp (Or.inl rfl)
    have hi := rel_subst_left p (paramsUp (paramsUp ρ)) d.castSucc.castSucc (Fin.last m).castSucc y.castSucc.castSucc
      (eq_symm (.conjL hB)) (add (add hy' E) B)
    exact rel_subst_right p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc y.castSucc.castSucc (Fin.last (m+1)) (eq_symm (.conjR hB)) hi

theorem append_checked {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (g k f d y b : Fin m)
    (hf : Derives Γ (checked p ρ f d b)) (hy : Derives Γ (rel p ρ d y))
    (ha : Derives Γ (append g k f d y b)) : Derives Γ (checked p ρ g k b) :=
  .conjI (.conjL ha) (appended_rows p ρ g f d y (.conjR hf) hy (.conjL (.conjR ha)))

theorem restricted_rows {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (g f d : Fin m)
    (hf : Derives Γ (rows p ρ f)) (hr : Derives Γ (RestrictionSyntax.restrict g f d)) : Derives Γ (rows p ρ g) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hf' : Derives Δ (rows p (paramsUp (paramsUp ρ)) f.castSucc.castSucc) := by
    simpa only [Formula.raise, rows_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hr' : Derives Δ (RestrictionSyntax.restrict g.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc) := by
    simpa only [Formula.raise, RestrictionSyntax.restrict_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hr)
  apply Derives.impI
  exact .impE (add (rows_at p (paramsUp (paramsUp ρ)) f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hf') _)
    (RestrictionEdges.old_edge g.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add hr' _) (.hyp (Or.inl rfl)))

theorem prefix_checked {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (g f d k b : Fin m)
    (hf : Derives Γ (checked p ρ f d b)) (hg : Derives Γ (SequencePrefix.witness g f k b)) :
    Derives Γ (checked p ρ g k b) := .conjI (.conjL hg) (restricted_rows p ρ g f k (.conjR hf) (.conjL (.conjR hg)))
end PPAC.Migration.Internal.CheckedSequence
