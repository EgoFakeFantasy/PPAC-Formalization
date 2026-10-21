import PPAC.Migration.HierarchyHistory

/-! 层成员递归的纯对象存在式；索引、历史输出及子集均为内部集合。 -/
namespace PPAC.Migration.HierarchyMemberSyntax
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax HierarchyLayerSyntax

def graphData {m} (a h z b v : Fin m) : Formula m :=
  (Formula.mem b a).conj ((edge h b v).conj (subset z v))

def layerData {m} (a z b v : Fin m) : Formula m :=
  (Formula.mem b a).conj ((layer b v).conj (subset z v))

def graphMember {m} (a h z : Fin m) : Formula m := .ex (.ex
  (graphData a.castSucc.castSucc h.castSucc.castSucc z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1))))

def layerMember {m} (a z : Fin m) : Formula m := .ex (.ex
  (layerData a.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))

def membership {m} (a y : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) y.castSucc).iff (layerMember a.castSucc (Fin.last m)))

theorem graphData_rename {m k} (a h z b v : Fin m) (r : Fin m → Fin k) :
    (graphData a h z b v).rename r = graphData (r a) (r h) (r z) (r b) (r v) := by
  simp only [graphData, Formula.rename, edge_rename, subset_rename]

theorem layerData_rename {m k} (a z b v : Fin m) (r : Fin m → Fin k) :
    (layerData a z b v).rename r = layerData (r a) (r z) (r b) (r v) := by
  simp only [layerData, Formula.rename, layer_rename, subset_rename]

theorem graphMember_rename {m k} (a h z : Fin m) (r : Fin m → Fin k) :
    (graphMember a h z).rename r = graphMember (r a) (r h) (r z) := by
  simp only [graphMember, Formula.rename, graphData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem layerMember_rename {m k} (a z : Fin m) (r : Fin m → Fin k) :
    (layerMember a z).rename r = layerMember (r a) (r z) := by
  simp only [layerMember, Formula.rename, layerData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem membership_rename {m k} (a y : Fin m) (r : Fin m → Fin k) :
    (membership a y).rename r = membership (r a) (r y) := by
  simp only [membership, Formula.rename, Formula.iff, layerMember_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_graphMember {m} {Γ : Context m} (a h z b v : Fin m)
    (hw : Derives Γ (graphData a h z b v)) : Derives Γ (graphMember a h z) := by
  apply Derives.exI b
  apply Derives.exI v
  simp only [Formula.instantiate, graphData_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact hw

abbrev graphMemberWitnesses {m} (a h z : Fin m) : Formula (m+2) :=
  graphData a.castSucc.castSucc h.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

theorem eliminate_graphMember {m} {Γ : Context m} (a h z : Fin m) (q : Formula m)
    (hh : Derives Γ (graphMember a h z))
    (hc : Derives (Context.add (graphMemberWitnesses a h z)
      (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (graphMemberWitnesses a h z))) at hh
  apply Derives.exE hh
  apply Derives.exE (p := graphMemberWitnesses a h z) (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨t, ht, heq⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨t, Or.inr ht, heq⟩

theorem intro_layerMember {m} {Γ : Context m} (a z b v : Fin m)
    (hw : Derives Γ (layerData a z b v)) : Derives Γ (layerMember a z) := by
  apply Derives.exI b
  apply Derives.exI v
  simp only [Formula.instantiate, layerData_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact hw

abbrev layerMemberWitnesses {m} (a z : Fin m) : Formula (m+2) :=
  layerData a.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

theorem eliminate_layerMember {m} {Γ : Context m} (a z : Fin m) (q : Formula m)
    (hh : Derives Γ (layerMember a z))
    (hc : Derives (Context.add (layerMemberWitnesses a z)
      (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (layerMemberWitnesses a z))) at hh
  apply Derives.exE hh
  apply Derives.exE (p := layerMemberWitnesses a z) (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨t, ht, heq⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨t, Or.inr ht, heq⟩

theorem membership_at {m} {Γ : Context m} (a y z : Fin m) (hh : Derives Γ (membership a y)) :
    Derives Γ ((Formula.mem z y).iff (layerMember a z)) := by
  have hi := Derives.allE z hh
  simpa only [Formula.instantiate, Formula.rename, layerMember_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.HierarchyMemberSyntax
