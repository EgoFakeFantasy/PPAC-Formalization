import PPAC.Migration.Internal.StructuralListLengthStep

/-! 在实际内部ω上作成员归纳，以严格尾码下降证明长度唯一性。 -/
namespace PPAC.Migration.Internal.StructuralListLengthUnique
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListTraceSyntax StructuralListLengthSyntax StructuralListLengthStep
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  have hi2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, earlier_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hi)
  apply Derives.impI
  apply Derives.impI
  exact unique_step (ZFContext.add (ZFContext.add hZ2 _) _) _ _ _ _ (add (add hw2 _) _) (add (add hi2 _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive StructuralListLengthSyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, StructuralListLengthSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using add (add (Derives.rename Fin.castSucc hw) M) I
  exact property_from_earlier hZ1 _ _ hw1 (.hyp (Or.inl rfl))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have h := BoundedInduction.induction_on_set StructuralListLengthSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ StructuralListLengthSyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w hw)
  simpa only [BoundedInduction.holds, StructuralListLengthSyntax.matrix_pred, paramsUp] using h

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (property w n) := by
  have h : Derives Γ ((Formula.mem n w).imp (property w n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE n (all_properties hZ w hw)
  exact .impE h hn

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l k : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (hasLength w n l)) (hk : Derives Γ (hasLength w n k)) : Derives Γ (.equal l k) := by
  have hn := StructuralListLengthBasic.code_member w n l hl
  exact property_at w n l k (at_code hZ w n hw hn) hl hk
end PPAC.Migration.Internal.StructuralListLengthUnique
