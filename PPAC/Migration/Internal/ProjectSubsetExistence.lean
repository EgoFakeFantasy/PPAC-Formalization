import PPAC.Migration.Internal.ProjectSubsetFinish

/-! Actual subset template code exists with every intermediate code and scope internal. -/
namespace PPAC.Migration.Internal.ProjectSubsetExistence
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectSubsetSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z x y : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hx : Derives Γ (SyntaxTermSyntax.branch true w b x)) (hy : Derives Γ (SyntaxTermSyntax.branch true w b y)) :
    Derives Γ (existsOutput w b z x y) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  let K0 := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) b.castSucc)
  let Γ1 := Context.add K0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := K0) (Derives.impE (OmegaSyntax.step_at w b (.conjL hw)) hb)
  have hK0 : Derives Γ1 K0 := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ K0
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw K0)
  have hx1 : Derives Γ1 (SyntaxTermSyntax.branch true w.castSucc b.castSucc x.castSucc) := by
    simpa only [Formula.raise, SyntaxTermSyntax.branch_rename] using (under hx K0)
  let K1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (ProjectBoundShiftSyntax.shifted w.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1)))
  let Γ2 := Context.add K1 (Context.image Formula.raise Γ1)
  apply Derives.exE (p := K1) (ProjectBoundShiftExistence.exists_output hZ1 w.castSucc b.castSucc x.castSucc hw1 hx1)
  have hK1 : Derives Γ2 K1 := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 K1
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 K1)
  have hy2 : Derives Γ2 (SyntaxTermSyntax.branch true w.castSucc.castSucc b.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, SyntaxTermSyntax.branch_rename] using (under (under hy K0) K1)
  let K2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (ProjectBoundShiftSyntax.shifted w.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Γ3 := Context.add K2 (Context.image Formula.raise Γ2)
  apply Derives.exE (p := K2) (ProjectBoundShiftExistence.exists_output hZ2 w.castSucc.castSucc b.castSucc.castSucc y.castSucc.castSucc hw2 hy2)
  have hK2 : Derives Γ3 K2 := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 K2
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 K2)
  have hzW3 : Derives Γ3 (.mem z.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, Formula.rename] using (under (under (under hzW K0) K1) K2)
  let K3 := (Formula.mem (Fin.last (m+3)) w.castSucc.castSucc.castSucc.castSucc).conj (SyntaxVariableSyntax.code true w.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)))
  let Γ4 := Context.add K3 (Context.image Formula.raise Γ3)
  apply Derives.exE (p := K3) (SyntaxVariables.exists_code hZ3 true w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc hw3 hzW3)
  have hK3 : Derives Γ4 K3 := .hyp (Or.inl rfl)
  have hZ4 := ZFContext.under hZ3 K3
  have hw4 := of_eq (omega_rename w.castSucc.castSucc.castSucc Fin.castSucc) (under hw3 K3)
  let K4 := (Formula.mem (Fin.last (m+4)) w.castSucc.castSucc.castSucc.castSucc.castSucc).conj (SyntaxAtomSyntax.zeroScalar w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)))
  let Γ5 := Context.add K4 (Context.image Formula.raise Γ4)
  apply Derives.exE (p := K4) (SyntaxConstructors.exists_constructor hZ4 0 0 w.castSucc.castSucc.castSucc.castSucc Fin.elim0 hw4 (Derives.eqRefl w.castSucc.castSucc.castSucc.castSucc))
  have hK4 : Derives Γ5 K4 := .hyp (Or.inl rfl)
  have hZ5 := ZFContext.under hZ4 K4
  have hw5 := of_eq (omega_rename w.castSucc.castSucc.castSucc.castSucc Fin.castSucc) (under hw4 K4)
  have h0 : Derives Γ5 (successor (Fin.last m).castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using (under (under (under (under (Derives.conjR hK0) K1) K2) K3) K4)
  have h1 : Derives Γ5 (ProjectBoundShiftSyntax.shifted w.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, ProjectBoundShiftSyntax.shifted_rename] using (under (under (under (Derives.conjR hK1) K2) K3) K4)
  have h2 : Derives Γ5 (ProjectBoundShiftSyntax.shifted w.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc) := by
    simpa only [Formula.raise, ProjectBoundShiftSyntax.shifted_rename] using (under (under (Derives.conjR hK2) K3) K4)
  have h3 : Derives Γ5 (SyntaxVariableSyntax.code true w.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc) := by
    simpa only [Formula.raise, SyntaxVariableSyntax.code_rename] using (under (Derives.conjR hK3) K4)
  have h4 : Derives Γ5 (SyntaxAtomSyntax.zeroScalar w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4))) := by
    simpa only [Formula.raise, SyntaxAtomSyntax.zeroScalar_rename] using (Derives.conjR hK4)
  let e : Fin 5 → Fin (m+5) := fun i => match i.val with
    | 0 => (Fin.last m).castSucc.castSucc.castSucc.castSucc | 1 => (Fin.last (m+1)).castSucc.castSucc.castSucc | 2 => (Fin.last (m+2)).castSucc.castSucc | 3 => (Fin.last (m+3)).castSucc | _ => (Fin.last (m+4))
  have hp : Derives Γ5 (ProjectSubsetFinish.prepared w.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc e) := .conjI h0 (.conjI h1 (.conjI h2 (.conjI h3 h4)))
  have ho := ProjectSubsetFinish.finish (Γ := Γ5) hZ5 w.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc e hw5 hp
  exact of_eq (by simp only [Formula.raise, existsOutput_rename]) ho

theorem exists_unique_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z x y : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hx : Derives Γ (SyntaxTermSyntax.branch true w b x)) (hy : Derives Γ (SyntaxTermSyntax.branch true w b y)) :
    Derives Γ (fiber w b z x y) := by
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (expanded w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (exists_output hZ w b z x y hw hb hz hx hy)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ Q
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hb1 : Derives Δ (.mem b.castSucc w.castSucc) := under hb Q
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz Q)
  have hx1 := of_eq (SyntaxTermSyntax.branch_rename true w b x Fin.castSucc) (under hx Q)
  have hy1 := of_eq (SyntaxTermSyntax.branch_rename true w b y Fin.castSucc) (under hy Q)
  have ht := ProjectSubsetLaws.target_type hZ1 w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m) hw1 hb1 hz1 hx1 hy1 (.conjR hQ)
  have hu := ProjectSubsetLaws.unique_output hZ1 w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m) hw1 (.conjR hQ)
  have ho : Derives Δ (fiber w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Q, Formula.instantiate, Formula.rename, expanded_rename, FormulaCodeSyntax.formulaCode_rename,
      uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjI hQ ht) hu)
  exact of_eq (fiber_rename w b z x y Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProjectSubsetExistence
