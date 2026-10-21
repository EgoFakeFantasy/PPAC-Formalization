import PPAC.Migration.GraphSyntax

/-! 原对象图关系的引入/消去与对象等词替换，不增添演算规则。 -/
namespace PPAC.Migration.GraphLogic
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax

theorem ordered_subst_object {m} {Γ : Context m} (p x y z : Fin m)
    (he : Derives Γ (.equal p z)) (hp : Derives Γ (ordered p x y)) :
    Derives Γ (ordered z x y) := by
  have hi : Derives Γ ((ordered (Fin.last m) x.castSucc y.castSucc).instantiate p) := by
    simpa only [Formula.instantiate, ordered_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have h := Derives.eqSubst (ordered (Fin.last m) x.castSucc y.castSucc) he hi
  simpa only [Formula.instantiate, ordered_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem ordered_subst_left {m} {Γ : Context m} (p x y z : Fin m)
    (he : Derives Γ (.equal x z)) (hp : Derives Γ (ordered p x y)) :
    Derives Γ (ordered p z y) := by
  have hi : Derives Γ ((ordered p.castSucc (Fin.last m) y.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, ordered_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have h := Derives.eqSubst (ordered p.castSucc (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, ordered_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem ordered_subst_right {m} {Γ : Context m} (p x y z : Fin m)
    (he : Derives Γ (.equal y z)) (hp : Derives Γ (ordered p x y)) :
    Derives Γ (ordered p x z) := by
  have hi : Derives Γ ((ordered p.castSucc x.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, ordered_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have h := Derives.eqSubst (ordered p.castSucc x.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, ordered_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem edge_intro {m} {Γ : Context m} (f x y p : Fin m)
    (hm : Derives Γ (.mem p f)) (hp : Derives Γ (ordered p x y)) : Derives Γ (edge f x y) := by
  apply Derives.exI p
  simpa only [Formula.instantiate, Formula.rename, ordered_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hm hp

theorem edge_elim {m} {Γ : Context m} (f x y : Fin m) (q : Formula m)
    (he : Derives Γ (edge f x y))
    (hc : Derives (Context.add ((Formula.mem (Fin.last m) f.castSucc).conj
      (ordered (Fin.last m) x.castSucc y.castSucc)) (Context.image Formula.raise Γ)) q.raise) :
    Derives Γ q := Derives.exE he hc

theorem entry_intro {m} {Γ : Context m} (d p x y : Fin m)
    (hx : Derives Γ (.mem x d)) (hp : Derives Γ (ordered p x y)) : Derives Γ (entryOn d p) := by
  unfold entryOn
  apply Derives.exI x
  apply Derives.exI y
  simpa only [Formula.instantiate, Formula.rename, ordered_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hx hp

theorem value_exists {m} {Γ : Context m} (f x y : Fin m)
    (h : Derives Γ (valueAt f x y)) : Derives Γ (valueExists f x) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, valueAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem value_subst_input {m} {Γ : Context m} (f x y a : Fin m)
    (he : Derives Γ (.equal x a)) (hv : Derives Γ (valueAt f x y)) : Derives Γ (valueAt f a y) := by
  have hi : Derives Γ ((valueAt f.castSucc (Fin.last m) y.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, valueAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hv
  have h := Derives.eqSubst (valueAt f.castSucc (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, valueAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem singleton_member {m} {Γ : Context m} (f p z : Fin m)
    (hf : Derives Γ (pair f p p)) (hz : Derives Γ (.mem z f)) : Derives Γ (.equal z p) :=
  .disjE (UnorderedPairLogic.member_cases f p p z hf hz) (.hyp (Or.inl rfl)) (.hyp (Or.inl rfl))

abbrev entryWitnesses {m} (d p : Fin m) : Formula (m+2) :=
  (Formula.mem (Fin.last m).castSucc d.castSucc.castSucc).conj
    (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))

theorem entry_elim {m} {Γ : Context m} (d p : Fin m) (q : Formula m)
    (h : Derives Γ (entryOn d p))
    (hc : Derives (Context.add (entryWitnesses d p)
      (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (entryWitnesses d p))) at h
  apply Derives.exE h
  apply Derives.exE (p := entryWitnesses d p) (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  intro r hr
  rcases hr with hr | ⟨s, hs, he⟩
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.GraphLogic
