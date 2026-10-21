import PPAC.Migration.TaggedRowLogic

/-! 全部实际带标签行的精确内部族及其原Replacement矩阵。 -/
namespace PPAC.Migration.TaggedFamilySyntax
open Source SourceAlgebra SourceLogic TaggedRowSyntax

def matrix : Formula 2 := row 1 0

def image {m} (a r : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) a.castSucc).conj (row r.castSucc (Fin.last m)))

def family {m} (b a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) b.castSucc).iff (image a.castSucc (Fin.last m)))

def familyExists {m} (a : Fin m) : Formula m := .ex (family (Fin.last m) a.castSucc)

def admissible {m} (b a : Fin m) : Formula m := (family b a).conj
  ((ChoiceSyntax.familyNonempty b).conj (ChoiceSyntax.disjoint b))

def admissibleExists {m} (a : Fin m) : Formula m := .ex (admissible (Fin.last m) a.castSucc)

theorem image_rename {m k} (a r : Fin m) (f : Fin m → Fin k) :
    (image a r).rename f = image (f a) (f r) := by
  simp only [image, Formula.rename, row_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem family_rename {m k} (b a : Fin m) (f : Fin m → Fin k) :
    (family b a).rename f = family (f b) (f a) := by
  simp only [family, Formula.rename, Formula.iff, image_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem familyExists_rename {m k} (a : Fin m) (f : Fin m → Fin k) :
    (familyExists a).rename f = familyExists (f a) := by
  simp only [familyExists, Formula.rename, family_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem admissible_rename {m k} (b a : Fin m) (f : Fin m → Fin k) :
    (admissible b a).rename f = admissible (f b) (f a) := by
  simp only [admissible, Formula.rename, family_rename, ChoiceSyntax.familyNonempty_rename, ChoiceSyntax.disjoint_rename]

theorem admissibleExists_rename {m k} (a : Fin m) (f : Fin m → Fin k) :
    (admissibleExists a).rename f = admissibleExists (f a) := by
  simp only [admissibleExists, Formula.rename, admissible_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {m} (ρ : Fin 0 → Fin m) (x r : Fin m) : ReplacementPredicates.rel matrix ρ x r = row r x := by
  have h0 : Fin.lastCases r (Fin.lastCases x ρ) (0 : Fin 2) = x := by
    change Fin.lastCases r (Fin.lastCases x ρ) (Fin.last 0).castSucc = x
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  have h1 : Fin.lastCases r (Fin.lastCases x ρ) (1 : Fin 2) = r := by
    change Fin.lastCases r (Fin.lastCases x ρ) (Fin.last 1) = r
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, row_rename, h0, h1]

theorem matrix_fiber {m} (ρ : Fin 0 → Fin m) (x : Fin m) : ReplacementPredicates.fiber matrix ρ x = rowFiber x := by
  simp only [ReplacementPredicates.fiber, ReplacementPredicates.unique, matrix_rel, rowFiber, uniqueRow]

theorem matrix_image {m} (ρ : Fin 0 → Fin m) (a r : Fin m) : ReplacementPredicates.image matrix ρ a r = image a r := by
  simp only [ReplacementPredicates.image, matrix_rel, image]

theorem matrix_range {m} (ρ : Fin 0 → Fin m) (a b : Fin m) : ReplacementPredicates.exactImage matrix ρ a b = family b a := by
  simp only [ReplacementPredicates.exactImage, matrix_image, family]

theorem family_at {m} {Γ : Context m} (b a r : Fin m) (hf : Derives Γ (family b a)) :
    Derives Γ ((Formula.mem r b).iff (image a r)) := by
  have hi := Derives.allE r hf
  simpa only [Formula.instantiate, Formula.rename, image_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem intro_image {m} {Γ : Context m} (a r x : Fin m)
    (hx : Derives Γ (.mem x a)) (hr : Derives Γ (row r x)) : Derives Γ (image a r) := by
  apply Derives.exI x
  simp only [Formula.instantiate, Formula.rename, row_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hx hr

theorem eliminate_member {m} {Γ : Context m} (b a r : Fin m) (q : Formula m)
    (hf : Derives Γ (family b a)) (hr : Derives Γ (.mem r b))
    (hc : Derives (Context.add ((Formula.mem (Fin.last m) a.castSucc).conj (row r.castSucc (Fin.last m)))
      (Context.image Formula.raise Γ)) q.raise) : Derives Γ q :=
  Derives.exE (.impE (.conjL (family_at b a r hf)) hr) hc
end PPAC.Migration.TaggedFamilySyntax
