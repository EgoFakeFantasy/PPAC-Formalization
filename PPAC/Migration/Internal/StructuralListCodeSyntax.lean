import PPAC.Migration.Internal.ObjectStructuralListEncode

/-! 原列表码的全内部字段单射性质；比较全部实际长度、任意码及所有输出对象。 -/
namespace PPAC.Migration.Internal.StructuralListCodeSyntax
open Source SourceAlgebra SourceLogic StructuralListSyntax StructuralListLengthSyntax StructuralListFieldSyntax

def agree {m} (w r a b : Fin m) : Formula m := .all (.all
  ((Formula.mem (Fin.last m).castSucc r.castSucc.castSucc).imp
    ((field w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      (field w.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def property {m} (w r : Fin m) : Formula m := .all (.all
  ((hasLength w.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc).imp
    ((hasLength w.castSucc.castSucc (Fin.last (m+1)) r.castSucc.castSucc).imp
      ((agree w.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last m).castSucc (Fin.last (m+1)))))))

def matrix : Formula 2 := property 0 1

def consViewBody {m} (w n r : Fin m) : Formula (m+2) :=
  ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (hasLength w.castSucc.castSucc (Fin.last (m+1)) r.castSucc.castSucc)).conj
    (consCode w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc)

def consView {m} (w n r : Fin m) : Formula m := .ex (.ex (consViewBody w n r))

theorem agree_rename {m k} (w r a b : Fin m) (s : Fin m → Fin k) : (agree w r a b).rename s = agree (s w) (s r) (s a) (s b) := by
  simp only [agree, Formula.rename, Formula.iff, field_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_rename {m k} (w r : Fin m) (s : Fin m → Fin k) : (property w r).rename s = property (s w) (s r) := by
  simp only [property, Formula.rename, hasLength_rename, agree_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem consView_rename {m k} (w n r : Fin m) (s : Fin m → Fin k) : (consView w n r).rename s = consView (s w) (s n) (s r) := by
  simp only [consView, consViewBody, Formula.rename, hasLength_rename, consCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 2) = x := by
    change Fin.lastCases x ρ (Fin.last 1) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, property_rename, h0, h1]

theorem agree_at {m} {Γ : Context m} (w r a b i y : Fin m) (ha : Derives Γ (agree w r a b))
    (hi : Derives Γ (.mem i r)) : Derives Γ ((field w a i y).iff (field w b i y)) := by
  have h : Derives Γ ((Formula.mem i r).imp ((field w a i y).iff (field w b i y))) := by
    simpa only [agree, Formula.instantiate, Formula.rename, Formula.iff, field_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE i ha)
  exact .impE h hi

theorem property_at {m} {Γ : Context m} (w r a b : Fin m) (hp : Derives Γ (property w r))
    (ha : Derives Γ (hasLength w a r)) (hb : Derives Γ (hasLength w b r)) (he : Derives Γ (agree w r a b)) : Derives Γ (.equal a b) := by
  have h : Derives Γ ((hasLength w a r).imp ((hasLength w b r).imp ((agree w r a b).imp (.equal a b)))) := by
    simpa only [property, Formula.instantiate, Formula.rename, hasLength_rename, agree_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE b (Derives.allE a hp)
  exact .impE (.impE (.impE h ha) hb) he

theorem intro_view {m} {Γ : Context m} (w n r h t : Fin m) (hh : Derives Γ (.mem h w))
    (ht : Derives Γ (hasLength w t r)) (hc : Derives Γ (consCode w h t n)) : Derives Γ (consView w n r) := by
  apply Derives.exI h
  apply Derives.exI t
  simp only [Formula.instantiate, consViewBody, Formula.rename, hasLength_rename, consCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hh ht) hc

theorem eliminate_view {m} {Γ : Context m} (w n r : Fin m) (q : Formula m) (hv : Derives Γ (consView w n r))
    (hc : Derives (Context.add (consViewBody w n r) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (consViewBody w n r))) at hv
  apply Derives.exE hv
  apply Derives.exE (p := consViewBody w n r) (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, hs, he⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.Internal.StructuralListCodeSyntax
