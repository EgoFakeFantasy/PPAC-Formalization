import PPAC.Migration.Internal.SyntaxTermImagePrefixExistence

/-! 源头槽关系的实际Replacement唯一纤维、全域总性与合法目标项模式。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePrefixTotal
open Source SourceAlgebra SourceLogic OmegaSyntax ReplacementPredicates SyntaxRenameQuerySyntax SyntaxTermImagePrefixSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem point_fiber {p m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f a z : Fin p) (ρ : Fin p → Fin m)
    (w c d A i : Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (imageMap w (ρ f) (ρ a) c d))
    (hA : Derives Γ (successor A (ρ a))) (hi : Derives Γ (.mem i A)) : Derives Γ (fiber (matrix f a z) ρ i) := by
  have he : Derives Γ (hasValue (matrix f a z) ρ i) :=
    of_eq (by simp only [hasValue, matrix_rel, paramsUp])
      (SyntaxTermImagePrefixExistence.point_exists hZ w (ρ f) (ρ a) c d (ρ z) A i hw hf hA hi)
  let Y := rel (matrix f a z) (paramsUp ρ) i.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) he
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (unique (matrix f a z) (paramsUp ρ) i.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let Z := rel (matrix f a z) (paramsUp (paramsUp ρ)) i.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Y) Z
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw Y) Z)
    have hf2 : Derives Δ (imageMap w.castSucc.castSucc (ρ f).castSucc.castSucc (ρ a).castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, imageMap_rename]) (under (under hf Y) Z)
    have hy2 : Derives Δ (value (ρ f).castSucc.castSucc (ρ a).castSucc.castSucc (ρ z).castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [Y, Formula.raise, matrix_rel, value_rename, paramsUp]) (under hY Z)
    have hz2 : Derives Δ (value (ρ f).castSucc.castSucc (ρ a).castSucc.castSucc (ρ z).castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))) :=
      of_eq (by simp only [Z, matrix_rel, paramsUp]) (Derives.hyp (Or.inl rfl) : Derives Δ Z)
    exact SyntaxTermImagePrefixUnique.unique hZ2 _ _ _ _ _ _ _ _ _ hw2 hf2 hz2 hy2
  have ho : Derives Ξ (fiber (matrix f a z) (paramsUp ρ) i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Y, Formula.instantiate, Formula.rename, rel_rename, unique_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hY hu)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem total {p m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f a z : Fin p) (ρ : Fin p → Fin m)
    (w c d A : Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (imageMap w (ρ f) (ρ a) c d))
    (hA : Derives Γ (successor A (ρ a))) : Derives Γ (ReplacementPredicates.total (matrix f a z) ρ A) := by
  apply Derives.allI
  apply Derives.impI
  let I := Formula.mem (Fin.last m) A.castSucc
  let Δ := Context.add I (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw I)
  have hf1 : Derives Δ (imageMap w.castSucc (ρ f).castSucc (ρ a).castSucc c.castSucc d.castSucc) :=
    of_eq (imageMap_rename w (ρ f) (ρ a) c d Fin.castSucc) (under hf I)
  have hA1 : Derives Δ (successor A.castSucc (ρ a).castSucc) := of_eq (successor_rename A (ρ a) Fin.castSucc) (under hA I)
  exact point_fiber (ZFContext.under hZ I) f a z (paramsUp ρ) w.castSucc c.castSucc d.castSucc A.castSucc (Fin.last m) hw1 hf1 hA1 (.hyp (Or.inl rfl))

theorem typed_outputs {p m} {Γ : Context m} (f a z : Fin p) (ρ : Fin p → Fin m) (w c d A : Fin m)
    (hf : Derives Γ (imageMap w (ρ f) (ρ a) c d)) (hz : Derives Γ (SyntaxTermSyntax.term w c d (ρ z))) :
    Derives Γ (SyntaxTermImageGraph.outputsTyped (matrix f a z) ρ w A c d) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := (Formula.mem (Fin.last m).castSucc A.castSucc.castSucc).conj
    (rel (matrix f a z) (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hf2 : Derives Δ (imageMap w.castSucc.castSucc (ρ f).castSucc.castSucc (ρ a).castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, imageMap_rename]) (SyntaxRenameBinders.under_2 hf H)
  have hz2 : Derives Δ (SyntaxTermSyntax.term w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (ρ z).castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (SyntaxRenameBinders.under_2 hz H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hv : Derives Δ (value (ρ f).castSucc.castSucc (ρ a).castSucc.castSucc (ρ z).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) :=
    of_eq (by simp only [matrix_rel, paramsUp]) (.conjR hH)
  exact SyntaxTermImagePrefixPoint.target_type _ _ _ _ _ _ _ _ hf2 hz2 hv

end PPAC.Migration.Internal.SyntaxTermImagePrefixTotal
