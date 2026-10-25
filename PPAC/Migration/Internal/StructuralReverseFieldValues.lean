import PPAC.Migration.Internal.StructuralReverseFieldSyntax

/-! Every internal reverse position has an actual natural source field, uniquely over all candidates. -/
namespace PPAC.Migration.Internal.StructuralReverseFieldValues
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralReverseIndexSyntax StructuralReverseFieldSyntax
open StructuralListFieldSyntax (field field_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l i y : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w n l i y)) : Derives Γ (.mem y w) := by
  let R := (mirror w.castSucc l.castSucc i.castSucc (Fin.last m)).conj (field w.castSucc n.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hv
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  exact StructuralListFieldValues.range (ZFContext.under hZ R) _ _ _ _ hw1 (.conjR hR)

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l i : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hi : Derives Γ (.mem i l)) : Derives Γ (existsValue w n l i) := by
  let R := mirror w.castSucc l.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralReverseIndexExistence.exists_partner hZ w l i hw hl hi)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hex := StructuralListFieldValues.exists_value hZ1 w.castSucc n.castSucc (Fin.last m) hw1 (.conjL (.conjR hR))
  let T := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hex
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hM := of_eq (mirror_rename w.castSucc l.castSucc i.castSucc (Fin.last m) Fin.castSucc) (under hR T)
  have hv := intro_value _ _ _ _ _ _ hM (.conjR hT)
  have hout : Derives Ξ (existsValue w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc i.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,value_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hT) hv)
  simpa only [Formula.raise,existsValue_rename] using hout

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l i y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (value w n l i y)) (hz : Derives Γ (value w n l i z)) : Derives Γ (.equal y z) := by
  let R := (mirror w.castSucc l.castSucc i.castSucc (Fin.last m)).conj (field w.castSucc n.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hy
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hz1 := of_eq (value_rename w n l i z Fin.castSucc) (under hz R)
  let T := (mirror w.castSucc.castSucc l.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).conj
    (field w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) z.castSucc.castSucc)
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hz1
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ R) T
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) T)
  have hM := of_eq (mirror_rename w.castSucc l.castSucc i.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) T)
  have hY := of_eq (field_rename w.castSucc n.castSucc (Fin.last m) y.castSucc Fin.castSucc) (under (.conjR hR) T)
  have he := StructuralReverseIndexArithmetic.unique hZ2 _ _ _ _ _ hw2 hM (.conjL hT)
  have hYc := StructuralListFieldSyntax.index_subst _ _ _ _ _ he hY
  exact StructuralListFieldValues.unique hZ2 _ _ _ _ _ hw2 (.conjL (.conjR (.conjL hT))) hYc (.conjR hT)

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l i : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hi : Derives Γ (.mem i l)) : Derives Γ (valueFiber w n l i) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (value w.castSucc n.castSucc l.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (exists_value hZ w n l i hw hl hi)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hu : Derives Δ (.all ((value w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let T := value w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))
    let Ξ := Context.add T (Context.image Formula.raise Δ)
    have hZ2 := ZFContext.under (ZFContext.under hZ R) T
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) T)
    have hOld := of_eq (value_rename w.castSucc n.castSucc l.castSucc i.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) T)
    exact unique hZ2 _ _ _ _ _ _ hw2 (.hyp (Or.inl rfl)) hOld
  have hout : Derives Δ (valueFiber w.castSucc n.castSucc l.castSucc i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjR hR) hu)
  simpa only [Formula.raise,valueFiber_rename] using hout

end PPAC.Migration.Internal.StructuralReverseFieldValues
