import PPAC.Migration.Internal.StructuralListReverseUnique

/-! Every actual mirror equation normalizes the entire reverse-field existential to the original source field. -/
namespace PPAC.Migration.Internal.StructuralReverseFieldAtMirror
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralReverseIndexSyntax StructuralReverseFieldSyntax
open StructuralListFieldSyntax (field field_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem at_mirror {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l i j y : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (mirror w l i j)) :
    Derives Γ ((value w n l i y).iff (field w n j y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := value w n l i y
    let R := (mirror w.castSucc l.castSucc i.castSucc (Fin.last m)).conj (field w.castSucc n.castSucc (Fin.last m) y.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have hm1 := of_eq (mirror_rename w l i j Fin.castSucc) (under (add hm H) R)
    have he := StructuralReverseIndexArithmetic.unique hZ1 _ _ _ _ _ hw1 (.conjL hR) hm1
    simpa only [Formula.raise,field_rename] using StructuralListFieldSyntax.index_subst _ _ _ _ _ he (.conjR hR)
  · apply Derives.impI
    exact intro_value w n l i j y (add hm _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.StructuralReverseFieldAtMirror
