import PPAC.Migration.Internal.ObjectSyntaxAtoms

/-! 类型状态是内部上下文Kuratowski对集合；历史图读取和实际后继bound读取的纯对象AST。 -/
namespace PPAC.Migration.Internal.SyntaxContextReadSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax

def read {m} (h x b f : Fin m) : Formula m := .ex
  ((edge h.castSucc x.castSucc (Fin.last m)).conj (edge (Fin.last m) b.castSucc f.castSucc))

def advanced {m} (h x b f : Fin m) : Formula m := .ex
  ((successor (Fin.last m) b.castSucc).conj (read h.castSucc x.castSucc (Fin.last m) f.castSucc))

def check {m} (advance : Bool) (h x b f : Fin m) : Formula m :=
  if advance then advanced h x b f else read h x b f

theorem read_rename {m k} (h x b f : Fin m) (r : Fin m → Fin k) :
    (read h x b f).rename r = read (r h) (r x) (r b) (r f) := by
  simp only [read, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem advanced_rename {m k} (h x b f : Fin m) (r : Fin m → Fin k) :
    (advanced h x b f).rename r = advanced (r h) (r x) (r b) (r f) := by
  simp only [advanced, Formula.rename, successor_rename, read_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem check_rename {m k} (advance : Bool) (h x b f : Fin m) (r : Fin m → Fin k) :
    (check advance h x b f).rename r = check advance (r h) (r x) (r b) (r f) := by
  cases advance <;> simp only [check, Bool.false_eq_true, ↓reduceIte, read_rename, advanced_rename]

theorem intro_read {m} {Γ : Context m} (h x b f v : Fin m) (hv : Derives Γ (edge h x v))
    (hc : Derives Γ (edge v b f)) : Derives Γ (read h x b f) := by
  apply Derives.exI v
  simp only [Formula.instantiate, Formula.rename, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hv hc

theorem intro_advanced {m} {Γ : Context m} (h x b f k : Fin m) (hs : Derives Γ (successor k b))
    (hr : Derives Γ (read h x k f)) : Derives Γ (advanced h x b f) := by
  apply Derives.exI k
  simp only [Formula.instantiate, Formula.rename, successor_rename, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs hr

theorem read_subst_child {m} {Γ : Context m} (h x y b f : Fin m) (he : Derives Γ (.equal x y))
    (hr : Derives Γ (read h x b f)) : Derives Γ (read h y b f) := by
  have hi : Derives Γ ((read h.castSucc (Fin.last m) b.castSucc f.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
  have ho := Derives.eqSubst (read h.castSucc (Fin.last m) b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem read_subst_bound {m} {Γ : Context m} (h x b k f : Fin m) (he : Derives Γ (.equal b k))
    (hr : Derives Γ (read h x b f)) : Derives Γ (read h x k f) := by
  have hi : Derives Γ ((read h.castSucc x.castSucc (Fin.last m) f.castSucc).instantiate b) := by
    simpa only [Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
  have ho := Derives.eqSubst (read h.castSucc x.castSucc (Fin.last m) f.castSucc) he hi
  simpa only [Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem check_subst_child {m} {Γ : Context m} (advance : Bool) (h x y b f : Fin m) (he : Derives Γ (.equal x y))
    (hr : Derives Γ (check advance h x b f)) : Derives Γ (check advance h y b f) := by
  have hi : Derives Γ ((check advance h.castSucc (Fin.last m) b.castSucc f.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, check_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
  have ho := Derives.eqSubst (check advance h.castSucc (Fin.last m) b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, check_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.SyntaxContextReadSyntax
