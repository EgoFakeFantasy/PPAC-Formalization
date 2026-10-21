import PPAC.Migration.Internal.StructuralListCodeStep

/-! 原列表码由实际内部长度及完整字段唯一确定，原对象ω归纳闭合全部内部长度。 -/
namespace PPAC.Migration.Internal.StructuralListCodeInduction
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListCodeSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem empty_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a b : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty r)) (ha : Derives Γ (hasLength w a r))
    (hb : Derives Γ (hasLength w b r)) : Derives Γ (.equal a b) :=
  StructuralNil.unique hZ w a b hw (StructuralListLengthConstruct.nil_of_empty_length hZ w a r ha hz)
    (StructuralListLengthConstruct.nil_of_empty_length hZ w b r hb hz)

theorem property_empty {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty r)) : Derives Γ (property w r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let A := hasLength w.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc
  let B := hasLength w.castSucc.castSucc (Fin.last (m+1)) r.castSucc.castSucc
  let E := agree w.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.add B (Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) A) B) E
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise := add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)) A) B) E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hz2 : Derives Δ (empty r.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hz
  exact empty_point hZ2 _ _ _ _ hw2 hz2 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl)))

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (OmegaInductionSyntax.base StructuralListCodeSyntax.matrix ρ) := by
  simp only [OmegaInductionSyntax.base, StructuralListCodeSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let E := empty (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega (ρ 0).castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  exact property_empty (ZFContext.under hZ E) _ _ hw1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (OmegaInductionSyntax.step StructuralListCodeSyntax.matrix ρ (ρ 0)) := by
  simp only [OmegaInductionSyntax.step, StructuralListCodeSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc (ρ 0).castSucc.castSucc
  let I := property (ρ 0).castSucc.castSucc (Fin.last m).castSucc
  let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ := Context.add S (Context.add I (Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) M) I) S
  have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)) M) I) S
  exact StructuralListCodeStep.property_successor hZ2 _ _ _ hw2
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (.all ((Formula.mem (Fin.last m) (ρ 0).castSucc).imp (property (ρ 0).castSucc (Fin.last m)))) := by
  have h := OmegaInduction.induction_on_omega StructuralListCodeSyntax.matrix ρ (ρ 0)
    (ZFContext.separation hZ StructuralListCodeSyntax.matrix) hw (base hZ ρ hw) (step hZ ρ hw)
  simpa only [OmegaInductionSyntax.holds, StructuralListCodeSyntax.matrix_pred, paramsUp] using h

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (hasLength w a r)) (hb : Derives Γ (hasLength w b r))
    (he : Derives Γ (agree w r a b)) : Derives Γ (.equal a b) := by
  have hall := all_unique hZ (fun _ => w) hw
  have hp : Derives Γ ((Formula.mem r w).imp (property w r)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE r hall
  exact property_at w r a b (.impE hp (StructuralListLengthBasic.length_member w a r ha)) ha hb he
end PPAC.Migration.Internal.StructuralListCodeInduction
