import PPAC.Migration.Internal.SyntaxTermImagePushPoint

/-! 项像表逐值变换的原Replacement总单值义务和实际目标项范围。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePushExistence
open Source SourceAlgebra SourceLogic OmegaSyntax ReplacementPredicates SyntaxRenameQuerySyntax SyntaxTermImagePushSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem point_fiber {p m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D f : Fin p) (ρ : Fin p → Fin m) (a i : Fin m)
    (hw : Derives Γ (omega (ρ w))) (hf : Derives Γ (SyntaxTermImageSyntax.imageMap (ρ w) (ρ f) a (ρ c) (ρ d)))
    (hm : Derives Γ (SyntaxIndexMapSyntax.maps (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D))) (hi : Derives Γ (.mem i a)) :
    Derives Γ (fiber (matrix w R S c d C D f) ρ i) := by
  have he : Derives Γ (hasValue (matrix w R S c d C D f) ρ i) :=
    of_eq (by simp only [hasValue, matrix_rel, paramsUp])
      (SyntaxTermImagePushPoint.exists_value hZ (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ f) a i hw hf hm hi)
  let Y := rel (matrix w R S c d C D f) (paramsUp ρ) i.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) he
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (unique (matrix w R S c d C D f) (paramsUp ρ) i.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let Z := rel (matrix w R S c d C D f) (paramsUp (paramsUp ρ)) i.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Y) Z
    have hw2 : Derives Δ (omega (ρ w).castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw Y) Z)
    have hf2 : Derives Δ (SyntaxTermImageSyntax.imageMap (ρ w).castSucc.castSucc (ρ f).castSucc.castSucc a.castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.imageMap_rename]) (under (under hf Y) Z)
    have hy2 : Derives Δ (value (ρ w).castSucc.castSucc (ρ R).castSucc.castSucc (ρ S).castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc (ρ C).castSucc.castSucc (ρ D).castSucc.castSucc (ρ f).castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [Y, Formula.raise, matrix_rel, value_rename, paramsUp]) (under hY Z)
    have hz2 : Derives Δ (value (ρ w).castSucc.castSucc (ρ R).castSucc.castSucc (ρ S).castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc (ρ C).castSucc.castSucc (ρ D).castSucc.castSucc (ρ f).castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))) :=
      of_eq (by simp only [Z, matrix_rel, paramsUp]) (Derives.hyp (Or.inl rfl) : Derives Δ Z)
    exact SyntaxTermImagePushPoint.unique hZ2 (ρ w).castSucc.castSucc (ρ R).castSucc.castSucc (ρ S).castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc (ρ C).castSucc.castSucc (ρ D).castSucc.castSucc (ρ f).castSucc.castSucc a.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hw2
      (SyntaxTermImageSyntax.image_function _ _ _ _ _ hf2) hz2 hy2
  have ho : Derives Ξ (fiber (matrix w R S c d C D f) (paramsUp ρ) i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Y, Formula.instantiate, Formula.rename, rel_rename, unique_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hY hu)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem total_matrix {p m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D f : Fin p) (ρ : Fin p → Fin m) (a : Fin m)
    (hw : Derives Γ (omega (ρ w))) (hf : Derives Γ (SyntaxTermImageSyntax.imageMap (ρ w) (ρ f) a (ρ c) (ρ d)))
    (hm : Derives Γ (SyntaxIndexMapSyntax.maps (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D))) :
    Derives Γ (ReplacementPredicates.total (matrix w R S c d C D f) ρ a) := by
  apply Derives.allI
  apply Derives.impI
  let I := Formula.mem (Fin.last m) a.castSucc
  let Δ := Context.add I (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega (ρ w).castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw I)
  have hf1 : Derives Δ (SyntaxTermImageSyntax.imageMap (ρ w).castSucc (ρ f).castSucc a.castSucc (ρ c).castSucc (ρ d).castSucc) :=
    of_eq (SyntaxTermImageSyntax.imageMap_rename _ _ _ _ _ Fin.castSucc) (under hf I)
  have hm1 : Derives Δ (SyntaxIndexMapSyntax.maps (ρ w).castSucc (ρ R).castSucc (ρ S).castSucc (ρ c).castSucc (ρ d).castSucc (ρ C).castSucc (ρ D).castSucc) :=
    of_eq (SyntaxIndexMapSyntax.maps_rename _ _ _ _ _ _ _ Fin.castSucc) (under hm I)
  exact point_fiber (ZFContext.under hZ I) w R S c d C D f (paramsUp ρ) a.castSucc (Fin.last m) hw1 hf1 hm1 (.hyp (Or.inl rfl))

theorem typed_outputs {p m} {Γ : Context m} (w R S c d C D f : Fin p) (ρ : Fin p → Fin m) (a : Fin m) :
    Derives Γ (SyntaxTermImageGraph.outputsTyped (matrix w R S c d C D f) ρ (ρ w) a (ρ C) (ρ D)) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (rel (matrix w R S c d C D f) (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hv : Derives Δ (value (ρ w).castSucc.castSucc (ρ R).castSucc.castSucc (ρ S).castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc (ρ C).castSucc.castSucc (ρ D).castSucc.castSucc (ρ f).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) :=
    of_eq (by simp only [matrix_rel, paramsUp]) (.conjR hH)
  exact SyntaxTermImagePushPoint.target_type (ρ w).castSucc.castSucc (ρ R).castSucc.castSucc (ρ S).castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc (ρ C).castSucc.castSucc (ρ D).castSucc.castSucc (ρ f).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hv

end PPAC.Migration.Internal.SyntaxTermImagePushExistence
