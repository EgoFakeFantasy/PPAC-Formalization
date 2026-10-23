import PPAC.Migration.Internal.StrictLookupFailure

/-! 全部内部合法长度上的严格查表准确域，字段对照仅用于证明而非执行定义。 -/
namespace PPAC.Migration.Internal.StrictLookupDomainSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax StrictLookupSyntax
open SyntaxRenameQuerySyntax (of_eq)

def property {m} (w r : Fin m) : Formula m := .all (.all (.all
  ((StructuralListLengthSyntax.hasLength w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc r.castSucc.castSucc.castSucc).imp
    ((Formula.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc).imp
      ((returned w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).iff
        ((Formula.mem (Fin.last (m+1)).castSucc r.castSucc.castSucc.castSucc).conj
          (StructuralListFieldSyntax.field w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))))))

def matrix : Formula 2 := property (0 : Fin 1).castSucc (Fin.last 1)

theorem property_rename {m k} (w r : Fin m) (ρ : Fin m → Fin k) :
    (property w r).rename ρ = property (ρ w) (ρ r) := by
  simp only [property, Formula.rename, Formula.iff, StructuralListLengthSyntax.hasLength_rename, returned_rename, StructuralListFieldSyntax.field_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred matrix ρ x = property (ρ 0) x := by
  simp only [matrix, MinimalPredicates.pred, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem at_field {m} {Γ : Context m} (w r n i y : Fin m) (hp : Derives Γ (property w r))
    (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n r)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((returned w n i y).iff ((Formula.mem i r).conj (StructuralListFieldSyntax.field w n i y))) := by
  have hh : Derives Γ ((StructuralListLengthSyntax.hasLength w n r).imp ((Formula.mem i w).imp
      ((returned w n i y).iff ((Formula.mem i r).conj (StructuralListFieldSyntax.field w n i y))))) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, Formula.iff, StructuralListLengthSyntax.hasLength_rename, returned_rename, StructuralListFieldSyntax.field_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE y (Derives.allE i (Derives.allE n hp)))
  exact .impE (.impE hh hl) hi

theorem returned_output_subst {m} {Γ : Context m} (w n i y z : Fin m)
    (he : Derives Γ (.equal y z)) (hy : Derives Γ (returned w n i y)) : Derives Γ (returned w n i z) := by
  let P := returned w.castSucc n.castSucc i.castSucc (Fin.last m)
  have e0 : P.instantiate y = returned w n i y := by
    simp only [P, Formula.instantiate, returned_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z = returned w n i z := by
    simp only [P, Formula.instantiate, returned_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hy))

theorem returned_field {m} {Γ : Context m} (w n i y : Fin m) (hy : Derives Γ (returned w n i y)) :
    Derives Γ (StructuralListFieldSyntax.field w n i y) := by
  let B := StrictLookupSyntax.body w n i y
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (StructuralListFieldSyntax.field_rename w n i y Fin.castSucc).symm
    (StructuralListFieldSyntax.intro_field w.castSucc n.castSucc i.castSucc y.castSucc (Fin.last m) (.conjL hB) (.disjL (.conjR hB)))

end PPAC.Migration.Internal.StrictLookupDomainSyntax
