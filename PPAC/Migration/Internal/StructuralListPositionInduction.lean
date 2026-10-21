import PPAC.Migration.Internal.StructuralListPositionStep

/-! 全部内部ω索引上的原迹位置对应，由原Separationω归纳模式实际取得。 -/
namespace PPAC.Migration.Internal.StructuralListPositionInduction
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax StructuralListPositionSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 4 → Fin m) (d : Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hf : Derives Γ (sequence (ρ 2) d (ρ 0))) (hn : Derives Γ (edge (ρ 2) (ρ 1) (ρ 3))) :
    Derives Γ (OmegaInductionSyntax.base StructuralListPositionSyntax.matrix ρ) := by
  simp only [OmegaInductionSyntax.base, StructuralListPositionSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let E := empty (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ E
  have hw1 : Derives Δ (omega (ρ 0).castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hf1 : Derives Δ (sequence (ρ 2).castSucc d.castSucc (ρ 0).castSucc) := by simpa only [Formula.raise, sequence_rename] using under hf E
  have hn1 : Derives Δ (edge (ρ 2).castSucc (ρ 1).castSucc (ρ 3).castSucc) := by simpa only [Formula.raise, edge_rename] using under hn E
  exact StructuralListPositionBase.positions_empty hZ1 _ _ _ _ _ _ hw1 hf1 hn1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 4 → Fin m) (d : Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hf : Derives Γ (sequence (ρ 2) d (ρ 0)))
    (hl : Derives Γ (StructuralListTraceSyntax.links (ρ 0) (ρ 1) (ρ 2))) :
    Derives Γ (OmegaInductionSyntax.step StructuralListPositionSyntax.matrix ρ (ρ 0)) := by
  simp only [OmegaInductionSyntax.step, StructuralListPositionSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc (ρ 0).castSucc.castSucc
  let I := positions (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (ρ 2).castSucc.castSucc (ρ 3).castSucc.castSucc (Fin.last m).castSucc
  let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ := Context.add S (Context.add I (Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) M) I) S
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise :=
    add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hq)) M) I) S
  have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hf2 : Derives Δ (sequence (ρ 2).castSucc.castSucc d.castSucc.castSucc (ρ 0).castSucc.castSucc) := by
    simpa only [Formula.raise, sequence_rename] using lift hf
  have hl2 : Derives Δ (StructuralListTraceSyntax.links (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (ρ 2).castSucc.castSucc) := by
    simpa only [Formula.raise, StructuralListTraceSyntax.links_rename] using lift hl
  exact StructuralListPositionStep.positions_successor hZ2 _ _ _ _ _ _ _ hw2 hf2 hl2
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_positions {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 4 → Fin m) (d : Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hf : Derives Γ (sequence (ρ 2) d (ρ 0)))
    (hl : Derives Γ (StructuralListTraceSyntax.links (ρ 0) (ρ 1) (ρ 2))) (hn : Derives Γ (edge (ρ 2) (ρ 1) (ρ 3))) :
    Derives Γ (.all ((Formula.mem (Fin.last m) (ρ 0).castSucc).imp
      (positions (ρ 0).castSucc (ρ 1).castSucc (ρ 2).castSucc (ρ 3).castSucc (Fin.last m)))) := by
  have h := OmegaInduction.induction_on_omega StructuralListPositionSyntax.matrix ρ (ρ 0)
    (ZFContext.separation hZ StructuralListPositionSyntax.matrix) hw (base hZ ρ d hw hf hn) (step hZ ρ d hw hf hl)
  simpa only [OmegaInductionSyntax.holds, StructuralListPositionSyntax.matrix_pred, paramsUp] using h

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l d f n r : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f d w))
    (hl : Derives Γ (StructuralListTraceSyntax.links w l f)) (hn : Derives Γ (edge f l n))
    (hr : Derives Γ (.mem r w)) : Derives Γ (positions w l f n r) := by
  have hall := all_positions hZ (params w l f n) d
    (by simpa only [params_first] using hw) (by simpa only [params_graph, params_first] using hf)
    (by simpa only [params_first, params_length, params_graph] using hl)
    (by simpa only [params_graph, params_length, params_code] using hn)
  have h : Derives Γ ((Formula.mem r w).imp (positions w l f n r)) := by
    simpa only [Formula.instantiate, Formula.rename, positions_rename, Fin.lastCases_last, Fin.lastCases_castSucc,
      params_first, params_length, params_graph, params_code, id_eq] using Derives.allE r hall
  exact .impE h hr
end PPAC.Migration.Internal.StructuralListPositionInduction
