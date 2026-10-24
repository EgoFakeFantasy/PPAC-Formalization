import PPAC.Migration.Internal.ProjectAtomicLaws
import PPAC.Migration.Internal.OriginalUniversalBlock

/-! All internal atomic source codes have an actual unique well-typed output. -/
namespace PPAC.Migration.Internal.ProjectAtomicExistence
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectAtomicSyntax
open SyntaxRenameQuerySyntax (of_eq)
open OriginalUniversalBlock (allMany allMany_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem result_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z x y : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hx : Derives Γ (SyntaxTermSyntax.branch true w b x)) (hy : Derives Γ (SyntaxTermSyntax.branch true w b y)) :
    Derives Γ (existsResult kind w b z x y) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hX := ProjectAtomicLaws.bound_term w b z x hb hzW hx
  have hY := ProjectAtomicLaws.bound_term w b z y hb hzW hy
  rcases kind with ⟨k,hk⟩
  have h : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h with rfl | rfl | rfl
  · exact ProjectAtomicMember.exists_result hZ w b z x y hw hX hY
  · have hnX := SyntaxTerms.range hZ w b z x hw hX
    have hnY := SyntaxTerms.range hZ w b z y hw hY
    exact SyntaxConstructors.exists_constructor hZ 2 3 w (SyntaxAtomSyntax.two x y) hw (.conjI hnX (.conjI hnY (.eqRefl w)))
  · exact ProjectSubsetExistence.exists_output hZ w b z x y hw hb hz hx hy

theorem exists_unique_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z x y n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (sourceAt kind w b x y n)) :
    Derives Γ (fiber kind w b z x y n) := by
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (result kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (result_exists hZ kind w b z x y hw (.conjL hi) hz (.conjL (.conjR hi)) (.conjL (.conjR (.conjR hi))))
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ Q
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz Q)
  have hi1 := of_eq (sourceAt_rename kind w b x y n Fin.castSucc) (under hi Q)
  have hc : Derives Δ (compiled kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc (Fin.last m)) := .conjI hi1 (.conjR hQ)
  have ht := ProjectAtomicLaws.compiled_type hZ1 kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc (Fin.last m) hw1 hz1 hc
  have hu := ProjectAtomicLaws.unique_output hZ1 kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc (Fin.last m) hw1 hc
  have ho : Derives Δ (fiber kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, compiled_rename, FormulaCodeSyntax.formulaCode_rename,
      uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjI (.conjI (.conjL hQ) hc) ht) hu)
  exact of_eq (fiber_rename kind w b z x y n Fin.castSucc).symm ho

def allInputs {m} (kind : Fin 3) (w z : Fin m) : Formula m := allMany 4
  ((sourceAt kind (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).imp
    (fiber kind (old 4 w) (slot 4 0) (old 4 z) (slot 4 1) (slot 4 2) (slot 4 3)))

theorem allInputs_rename {m l} (kind : Fin 3) (w z : Fin m) (ρ : Fin m → Fin l) :
    (allInputs kind w z).rename ρ = allInputs kind (ρ w) (ρ z) := by
  simp only [allInputs, allMany_rename, Formula.rename, sourceAt_rename, fiber_rename, lift_old, lift_slot]

theorem all_internal_inputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (allInputs kind w z) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let P := sourceAt kind (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw P)
  have hz4 := of_eq (empty_rename z (old 4)) (HornBinderRules.under_body 4 hz P)
  exact exists_unique_typed (HornBinderRules.zf_body 4 hZ P) kind (old 4 w) (slot 4 0) (old 4 z)
    (slot 4 1) (slot 4 2) (slot 4 3) hw4 hz4 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.ProjectAtomicExistence
