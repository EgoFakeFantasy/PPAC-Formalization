import PPAC.Migration.HierarchyClosedInstances

/-! 内部零或极限索引及全部早层之并的成员式；不限制外部标准序数。 -/
namespace PPAC.Migration.HierarchyLimitSyntax
open Source SourceAlgebra SourceLogic OrdinalSyntax HierarchyLayerSyntax

def successorInside {m} (a b : Fin m) : Formula m := .ex
  ((OmegaSyntax.successor (Fin.last m) b.castSucc).conj (.mem (Fin.last m) a.castSucc))

def closedSuccessor {m} (a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) a.castSucc).imp (successorInside a.castSucc (Fin.last m)))

/-- 包含零：原序数且每个内部早期索引的实际后继仍在域内。 -/
def limitIndex {m} (a : Fin m) : Formula m := (ordinal a).conj (closedSuccessor a)

def unionData {m} (a z b v : Fin m) : Formula m :=
  (Formula.mem b a).conj ((layer b v).conj (.mem z v))

def unionMember {m} (a z : Fin m) : Formula m := .ex (.ex
  (unionData a.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))

def unionEquation {m} (a y : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) y.castSucc).iff (unionMember a.castSucc (Fin.last m)))

theorem successorInside_rename {m k} (a b : Fin m) (r : Fin m → Fin k) :
    (successorInside a b).rename r = successorInside (r a) (r b) := by
  simp only [successorInside, Formula.rename, OmegaSyntax.successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem closedSuccessor_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (closedSuccessor a).rename r = closedSuccessor (r a) := by
  simp only [closedSuccessor, Formula.rename, successorInside_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem limitIndex_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (limitIndex a).rename r = limitIndex (r a) := by
  simp only [limitIndex, Formula.rename, ordinal_rename, closedSuccessor_rename]

theorem unionData_rename {m k} (a z b v : Fin m) (r : Fin m → Fin k) :
    (unionData a z b v).rename r = unionData (r a) (r z) (r b) (r v) := by
  simp only [unionData, Formula.rename, layer_rename]

theorem unionMember_rename {m k} (a z : Fin m) (r : Fin m → Fin k) :
    (unionMember a z).rename r = unionMember (r a) (r z) := by
  simp only [unionMember, Formula.rename, unionData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem unionEquation_rename {m k} (a y : Fin m) (r : Fin m → Fin k) :
    (unionEquation a y).rename r = unionEquation (r a) (r y) := by
  simp only [unionEquation, Formula.rename, Formula.iff, unionMember_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem closed_at {m} {Γ : Context m} (a b : Fin m) (hc : Derives Γ (closedSuccessor a)) :
    Derives Γ ((Formula.mem b a).imp (successorInside a b)) := by
  have hi := Derives.allE b hc
  simpa only [Formula.instantiate, Formula.rename, successorInside_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem intro_unionMember {m} {Γ : Context m} (a z b v : Fin m)
    (hw : Derives Γ (unionData a z b v)) : Derives Γ (unionMember a z) := by
  apply Derives.exI b
  apply Derives.exI v
  simp only [Formula.instantiate, unionData_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact hw

abbrev unionWitnesses {m} (a z : Fin m) : Formula (m+2) :=
  unionData a.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

theorem eliminate_unionMember {m} {Γ : Context m} (a z : Fin m) (q : Formula m)
    (hh : Derives Γ (unionMember a z))
    (hc : Derives (Context.add (unionWitnesses a z)
      (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (unionWitnesses a z))) at hh
  apply Derives.exE hh
  apply Derives.exE (p := unionWitnesses a z) (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨t, ht, heq⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨t, Or.inr ht, heq⟩

theorem equation_at {m} {Γ : Context m} (a y z : Fin m) (hh : Derives Γ (unionEquation a y)) :
    Derives Γ ((Formula.mem z y).iff (unionMember a z)) := by
  have hi := Derives.allE z hh
  simpa only [Formula.instantiate, Formula.rename, unionMember_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.HierarchyLimitSyntax
