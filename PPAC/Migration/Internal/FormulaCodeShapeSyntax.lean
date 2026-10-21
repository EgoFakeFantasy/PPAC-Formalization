import PPAC.Migration.Internal.FormulaCodeConstructors

/-! 接受根码的实际完整Shape解码：标签、payload、实际长度及全部字段图的唯一纤维。 -/
namespace PPAC.Migration.Internal.FormulaCodeShapeSyntax
open Source SourceAlgebra SourceLogic StructuralTreeOperatorSyntax

def shapeBody {m} (w n : Fin m) : Formula (m+4) :=
  shape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3))

def uniqueShape {m} (w n t p l g : Fin m) : Formula m := .all (.all (.all (.all
  ((shapeBody w n).imp
    (((Formula.equal (Fin.last m).castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc).conj
      (.equal (Fin.last (m+1)).castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc)).conj
      ((Formula.equal (Fin.last (m+2)).castSucc l.castSucc.castSucc.castSucc.castSucc).conj
        (.equal (Fin.last (m+3)) g.castSucc.castSucc.castSucc.castSucc)))))))

def shapeFiber {m} (w n : Fin m) : Formula m := .ex (.ex (.ex (.ex
  ((shapeBody w n).conj (uniqueShape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3)))))))

theorem uniqueShape_rename {m k} (w n t p l g : Fin m) (s : Fin m → Fin k) :
    (uniqueShape w n t p l g).rename s = uniqueShape (s w) (s n) (s t) (s p) (s l) (s g) := by
  simp only [uniqueShape, shapeBody, Formula.rename, shape_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem shapeFiber_rename {m k} (w n : Fin m) (s : Fin m → Fin k) :
    (shapeFiber w n).rename s = shapeFiber (s w) (s n) := by
  simp only [shapeFiber, shapeBody, Formula.rename, shape_rename, uniqueShape_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} (w n t p l g : Fin m)
    (hs : Derives Γ (shape w n t p l g)) (hu : Derives Γ (uniqueShape w n t p l g)) :
    Derives Γ (shapeFiber w n) := by
  apply Derives.exI t
  apply Derives.exI p
  apply Derives.exI l
  apply Derives.exI g
  simp only [shapeBody, Formula.instantiate, Formula.rename, shape_rename, uniqueShape_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs hu

theorem eliminate_fiber {m} {Γ : Context m} (w n : Fin m) (q : Formula m)
    (he : Derives Γ (shapeFiber w n))
    (hc : Derives (Context.add
      ((shapeBody w n).conj (uniqueShape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
        (Fin.last (m+2)).castSucc (Fin.last (m+3))))
      (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))
      q.raise.raise.raise.raise) : Derives Γ q := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, ⟨t, ⟨u, hu, h1⟩, h2⟩, h3⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ⟨u, Or.inr hu, h1⟩, h2⟩, h3⟩
end PPAC.Migration.Internal.FormulaCodeShapeSyntax
