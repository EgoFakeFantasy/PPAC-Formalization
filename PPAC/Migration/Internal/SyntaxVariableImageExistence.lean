import PPAC.Migration.Internal.SyntaxVariableImagePoint

/-! 变量项码关系的实际Replacement总单值和目标合法性；不留下未来总性前提。 -/
namespace PPAC.Migration.Internal.SyntaxVariableImageExistence
open Source SourceAlgebra SourceLogic OmegaSyntax ReplacementPredicates SyntaxRenameQuerySyntax SyntaxVariableImageSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem point_fiber {p m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r c d : Fin p) (ρ : Fin p → Fin m) (a i : Fin m)
    (hw : Derives Γ (omega (ρ w))) (hi : Derives Γ (input bound (ρ w) (ρ r) a (ρ c) (ρ d))) (hm : Derives Γ (.mem i a)) :
    Derives Γ (fiber (matrix bound w r c d) ρ i) := by
  have he : Derives Γ (hasValue (matrix bound w r c d) ρ i) :=
    of_eq (by simp only [hasValue, matrix_rel, paramsUp])
      (SyntaxVariableImagePoint.exists_value hZ bound (ρ w) (ρ r) a (ρ c) (ρ d) i hw hi hm)
  let Y := rel (matrix bound w r c d) (paramsUp ρ) i.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) he
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (unique (matrix bound w r c d) (paramsUp ρ) i.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let Z := rel (matrix bound w r c d) (paramsUp (paramsUp ρ)) i.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Y) Z
    have hw2 : Derives Δ (omega (ρ w).castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw Y) Z)
    have hi2 : Derives Δ (input bound (ρ w).castSucc.castSucc (ρ r).castSucc.castSucc a.castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, input_rename]) (under (under hi Y) Z)
    have hy2 : Derives Δ (value bound (ρ w).castSucc.castSucc (ρ r).castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [Y, Formula.raise, matrix_rel, value_rename, paramsUp]) (under hY Z)
    have hz2 : Derives Δ (value bound (ρ w).castSucc.castSucc (ρ r).castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))) :=
      of_eq (by simp only [Z, matrix_rel, paramsUp]) (Derives.hyp (Or.inl rfl) : Derives Δ Z)
    exact SyntaxVariableImagePoint.unique hZ2 bound (ρ w).castSucc.castSucc (ρ r).castSucc.castSucc a.castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hw2 (.conjL (.conjR (.conjR hi2))) hz2 hy2
  have ho : Derives Ξ (fiber (matrix bound w r c d) (paramsUp ρ) i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Y, Formula.instantiate, Formula.rename, rel_rename, unique_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hY hu)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem total_matrix {p m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r c d : Fin p) (ρ : Fin p → Fin m) (a : Fin m)
    (hw : Derives Γ (omega (ρ w))) (hi : Derives Γ (input bound (ρ w) (ρ r) a (ρ c) (ρ d))) :
    Derives Γ (ReplacementPredicates.total (matrix bound w r c d) ρ a) := by
  apply Derives.allI
  apply Derives.impI
  let I := Formula.mem (Fin.last m) a.castSucc
  let Δ := Context.add I (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega (ρ w).castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw I)
  have hi1 : Derives Δ (input bound (ρ w).castSucc (ρ r).castSucc a.castSucc (ρ c).castSucc (ρ d).castSucc) :=
    of_eq (input_rename bound _ _ _ _ _ Fin.castSucc) (under hi I)
  exact point_fiber (ZFContext.under hZ I) bound w r c d (paramsUp ρ) a.castSucc (Fin.last m) hw1 hi1 (.hyp (Or.inl rfl))

theorem typed_outputs {p m} {Γ : Context m} (bound : Bool) (w r c d : Fin p) (ρ : Fin p → Fin m) (a : Fin m) :
    Derives Γ (SyntaxTermImageGraph.outputsTyped (matrix bound w r c d) ρ (ρ w) a (ρ c) (ρ d)) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (rel (matrix bound w r c d) (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hv : Derives Δ (value bound (ρ w).castSucc.castSucc (ρ r).castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) :=
    of_eq (by simp only [matrix_rel, paramsUp]) (.conjR hH)
  exact SyntaxVariableImagePoint.target_type bound (ρ w).castSucc.castSucc (ρ r).castSucc.castSucc (ρ c).castSucc.castSucc (ρ d).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hv
end PPAC.Migration.Internal.SyntaxVariableImageExistence
