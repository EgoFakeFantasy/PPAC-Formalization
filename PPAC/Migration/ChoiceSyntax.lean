import PPAC.Migration.CollectionFromReplacement

/-! 原图AC和原不交族选择集AC的纯对象展开；全部族、图和元素量词内部化。 -/
namespace PPAC.Migration.ChoiceSyntax
open Source SourceAlgebra SourceLogic GraphSyntax PairSyntax

def familyNonempty {m} (a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) a.castSucc).imp (MinimalPredicates.inhabited (Fin.last m)))

def intersection {m} (u v : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) u.castSucc).conj (.mem (Fin.last m) v.castSucc))

def disjoint {m} (a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) a.castSucc).imp (.all
    ((Formula.mem (Fin.last (m+1)) a.castSucc.castSucc).imp
      ((Formula.equal (Fin.last m).castSucc (Fin.last (m+1))).neg.imp
        (intersection (Fin.last m).castSucc (Fin.last (m+1))).neg))))

def chosen {m} (c u y : Fin m) : Formula m := (Formula.mem y c).conj (.mem y u)

def selected {m} (c u y : Fin m) : Formula m := (chosen c u y).conj (.all
  ((chosen c.castSucc u.castSucc (Fin.last m)).imp (.equal (Fin.last m) y.castSucc)))

def selectedExists {m} (c u : Fin m) : Formula m := .ex (selected c.castSucc u.castSucc (Fin.last m))

def selector {m} (c a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) a.castSucc).imp (selectedExists c.castSucc (Fin.last m)))

def selectorExists {m} (a : Fin m) : Formula m := .ex (selector (Fin.last m) a.castSucc)

def selectorAC : Source.Sentence := (((familyNonempty (0 : Fin 1)).conj (disjoint 0)).imp (selectorExists 0)).close

def choiceValue {m} (f u : Fin m) : Formula m := .ex
  ((edge f.castSucc u.castSucc (Fin.last m)).conj (.mem (Fin.last m) u.castSucc))

def choiceOn {m} (f a : Fin m) : Formula m := (functionOn f a).conj (.all
  ((Formula.mem (Fin.last m) a.castSucc).imp (choiceValue f.castSucc (Fin.last m))))

def graphExists {m} (a : Fin m) : Formula m := .ex (choiceOn (Fin.last m) a.castSucc)

theorem familyNonempty_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (familyNonempty a).rename r = familyNonempty (r a) := by
  simp only [familyNonempty, Formula.rename, MinimalPredicates.inhabited_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intersection_rename {m k} (u v : Fin m) (r : Fin m → Fin k) :
    (intersection u v).rename r = intersection (r u) (r v) := by
  simp only [intersection, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem disjoint_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (disjoint a).rename r = disjoint (r a) := by
  simp only [disjoint, Formula.rename, Formula.neg, intersection_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem chosen_rename {m k} (c u y : Fin m) (r : Fin m → Fin k) :
    (chosen c u y).rename r = chosen (r c) (r u) (r y) := by
  simp only [chosen, Formula.rename]

theorem selected_rename {m k} (c u y : Fin m) (r : Fin m → Fin k) :
    (selected c u y).rename r = selected (r c) (r u) (r y) := by
  simp only [selected, Formula.rename, chosen_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem selectedExists_rename {m k} (c u : Fin m) (r : Fin m → Fin k) :
    (selectedExists c u).rename r = selectedExists (r c) (r u) := by
  simp only [selectedExists, Formula.rename, selected_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem selector_rename {m k} (c a : Fin m) (r : Fin m → Fin k) :
    (selector c a).rename r = selector (r c) (r a) := by
  simp only [selector, Formula.rename, selectedExists_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem selectorExists_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (selectorExists a).rename r = selectorExists (r a) := by
  simp only [selectorExists, Formula.rename, selector_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem choiceValue_rename {m k} (f u : Fin m) (r : Fin m → Fin k) :
    (choiceValue f u).rename r = choiceValue (r f) (r u) := by
  simp only [choiceValue, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem choiceOn_rename {m k} (f a : Fin m) (r : Fin m → Fin k) :
    (choiceOn f a).rename r = choiceOn (r f) (r a) := by
  simp only [choiceOn, Formula.rename, functionOn_rename, choiceValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graphExists_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (graphExists a).rename r = graphExists (r a) := by
  simp only [graphExists, Formula.rename, choiceOn_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem nonempty_original {m} (u : Fin m) : Source.SetLanguage.nonempty u = MinimalPredicates.inhabited u := by
  change (MinimalPredicates.inhabited (0 : Fin 1)).rename (Source.SetLanguage.args1 u) = _
  rw [MinimalPredicates.inhabited_rename]
  rfl

theorem choiceOn_original {m} (f a : Fin m) : Source.SetLanguage.choiceOn f a = choiceOn f a := by
  simp only [Source.SetLanguage.choiceOn, functionOn_original, edge_original]
  change (choiceOn (0 : Fin 2) 1).rename (Source.SetLanguage.args2 f a) = _
  rw [choiceOn_rename, args2_first, args2_second]

theorem graphAC_original : Source.SetLanguage.AC = ((familyNonempty (0 : Fin 1)).imp (graphExists 0)).close := by
  simp only [Source.SetLanguage.AC, nonempty_original, choiceOn_original, familyNonempty, graphExists, Formula.close]
  rfl

theorem graph_ac_at {m} {Γ : Context m} (a : Fin m)
    (hc : Derives Γ (Source.SetLanguage.AC.rename Fin.elim0)) : Derives Γ ((familyNonempty a).imp (graphExists a)) := by
  rw [graphAC_original] at hc
  have hi := specialize_close ((familyNonempty (0 : Fin 1)).imp (graphExists 0)) (fun _ => a) hc
  simpa only [Formula.rename, familyNonempty_rename, graphExists_rename] using hi

theorem choice_at {m} {Γ : Context m} (f a u : Fin m) (hh : Derives Γ (choiceOn f a)) :
    Derives Γ ((Formula.mem u a).imp (choiceValue f u)) := by
  have hi := Derives.allE u (.conjR hh)
  simpa only [Formula.instantiate, Formula.rename, choiceValue_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem selector_at {m} {Γ : Context m} (c a u : Fin m) (hh : Derives Γ (selector c a)) :
    Derives Γ ((Formula.mem u a).imp (selectedExists c u)) := by
  have hi := Derives.allE u hh
  simpa only [Formula.instantiate, Formula.rename, selectedExists_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem disjoint_at {m} {Γ : Context m} (a u v : Fin m) (hh : Derives Γ (disjoint a)) :
    Derives Γ ((Formula.mem u a).imp ((Formula.mem v a).imp ((Formula.equal u v).neg.imp (intersection u v).neg))) := by
  have hu := Derives.allE u hh
  have hu' : Derives Γ ((Formula.mem u a).imp (.all ((Formula.mem (Fin.last m) a.castSucc).imp
      ((Formula.equal u.castSucc (Fin.last m)).neg.imp (intersection u.castSucc (Fin.last m)).neg)))) := by
    simpa only [Formula.instantiate, Formula.rename, Formula.neg, intersection_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hu
  apply Derives.impI
  have hv := Derives.allE v (.impE (add hu' _) (.hyp (Or.inl rfl)))
  simpa only [Formula.instantiate, Formula.rename, Formula.neg, intersection_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hv
end PPAC.Migration.ChoiceSyntax
