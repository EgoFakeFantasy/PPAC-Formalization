import PPAC.Migration.Internal.StructuralListFieldBoundsStep

/-! 原对象ω长度归纳关闭全部域内字段界，并组合完整字段图与父raw节点严格界。 -/
namespace PPAC.Migration.Internal.StructuralListFieldBounds
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListFieldSyntax StructuralListFieldGraphSyntax StructuralListFieldBoundsSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem property_empty {m} {Γ : Context m} (w r : Fin m) (hz : Derives Γ (empty r)) : Derives Γ (property w r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let L := hasLength w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc r.castSucc.castSucc.castSucc
  let M := Formula.mem (Fin.last (m+1)).castSucc r.castSucc.castSucc.castSucc
  let F := field w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
  let Δ := Context.add F (Context.add M (Context.add L (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))
  have hz3 : Derives Δ (empty r.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using add (add (add (OrdinalRestriction.raise_three hz) L) M) F
  exact .botE (.impE (empty_at _ _ hz3) (.hyp (Or.inr (Or.inl rfl))))

theorem base {m} {Γ : Context m} (ρ : Fin 1 → Fin m) : Derives Γ (OmegaInductionSyntax.base StructuralListFieldBoundsSyntax.matrix ρ) := by
  simp only [OmegaInductionSyntax.base, StructuralListFieldBoundsSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  exact property_empty _ _ (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (OmegaInductionSyntax.step StructuralListFieldBoundsSyntax.matrix ρ (ρ 0)) := by
  simp only [OmegaInductionSyntax.step, StructuralListFieldBoundsSyntax.matrix_pred, paramsUp]
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
  exact StructuralListFieldBoundsStep.property_successor hZ2 _ _ _ hw2
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have h := OmegaInduction.induction_on_omega StructuralListFieldBoundsSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ StructuralListFieldBoundsSyntax.matrix) hw (base (fun _ => w)) (step hZ (fun _ => w) hw)
  simpa only [OmegaInductionSyntax.holds, StructuralListFieldBoundsSyntax.matrix_pred, paramsUp] using h

theorem field_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l i y : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (hasLength w n l)) (hi : Derives Γ (.mem i l)) (hy : Derives Γ (field w n i y)) : Derives Γ (.mem y n) := by
  have hall := all_bounds hZ w hw
  have hp : Derives Γ ((Formula.mem l w).imp (property w l)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE l hall
  exact at_field w l n i y (.impE hp (StructuralListLengthBasic.length_member w n l hl)) hl hi hy

theorem edge_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l f i y : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (hasLength w n l)) (hf : Derives Γ (fields w n l f)) (he : Derives Γ (GraphSyntax.edge f i y)) : Derives Γ (.mem y n) := by
  have h := Derives.impE (.conjL (law_at w n l f i y (.conjR (.conjR hf)))) he
  exact field_member hZ w n l i y hw hl (.conjL h) (.conjR h)

theorem raw_field_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag p n l i y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hc : Derives Γ (StructuralNodeSyntax.raw w tag p n))
    (hl : Derives Γ (hasLength w p l)) (hi : Derives Γ (.mem i l)) (hy : Derives Γ (field w p i y)) : Derives Γ (.mem y n) := by
  have hn := StructuralNodeProperties.range hZ w tag p n hw hc
  have hp := StructuralListLengthBasic.code_member w p l hl
  have hpn := Derives.conjR (StructuralNodeProperties.components hZ w tag p n hw ht hp hc)
  exact StructuralListFieldBoundsStep.member_trans hZ w y p n hw hn (field_member hZ w p l i y hw hl hi hy) hpn

theorem raw_edge_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag p n l f i y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hc : Derives Γ (StructuralNodeSyntax.raw w tag p n))
    (hl : Derives Γ (hasLength w p l)) (hf : Derives Γ (fields w p l f)) (he : Derives Γ (GraphSyntax.edge f i y)) : Derives Γ (.mem y n) := by
  have h := Derives.impE (.conjL (law_at w p l f i y (.conjR (.conjR hf)))) he
  exact raw_field_member hZ w tag p n l i y hw ht hc hl (.conjL h) (.conjR h)
end PPAC.Migration.Internal.StructuralListFieldBounds
