import PPAC.Migration.Internal.BinaryUnionSyntax
import PPAC.Migration.Internal.PureSyntaxTraceExtension

/-! 合并两个真实纯语法闭轨迹；所有集合见证都在对象存在量词内取得。 -/
namespace PPAC.Migration.Internal.PureSyntaxTraceMerge
open Source SourceAlgebra SourceLogic PureSyntaxTrace
open SyntaxRenameQuerySyntax (of_eq)

def pairWitness {m} (w r s U : Fin m) : Formula m :=
  (RestrictionSyntax.subset U w).conj ((PureSyntaxTrace.closed w U).conj ((Formula.mem r U).conj (.mem s U)))

def pairCondition {m} (w r s : Fin m) : Formula m := .ex (pairWitness w.castSucc r.castSucc s.castSucc (Fin.last m))

theorem pairWitness_rename {m n} (w r s U : Fin m) (ρ : Fin m → Fin n) :
    (pairWitness w r s U).rename ρ = pairWitness (ρ w) (ρ r) (ρ s) (ρ U) := by
  simp only [pairWitness, Formula.rename, RestrictionSyntax.subset_rename, PureSyntaxTrace.closed_rename]

theorem pairCondition_rename {m n} (w r s : Fin m) (ρ : Fin m → Fin n) :
    (pairCondition w r s).rename ρ = pairCondition (ρ w) (ρ r) (ρ s) := by
  simp only [pairCondition, Formula.rename, pairWitness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem join_closed {m} {Γ : Context m} (w R S U : Fin m)
    (hu : Derives Γ (BinaryUnionSyntax.joined U R S))
    (hr : Derives Γ (PureSyntaxTrace.closed w R)) (hs : Derives Γ (PureSyntaxTrace.closed w S)) :
    Derives Γ (PureSyntaxTrace.closed w U) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) U.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hu1 : Derives Δ (BinaryUnionSyntax.joined U.castSucc R.castSucc S.castSucc) := of_eq (BinaryUnionSyntax.joined_rename U R S Fin.castSucc) (under hu M)
  have hr1 : Derives Δ (PureSyntaxTrace.closed w.castSucc R.castSucc) := of_eq (PureSyntaxTrace.closed_rename w R Fin.castSucc) (under hr M)
  have hs1 : Derives Δ (PureSyntaxTrace.closed w.castSucc S.castSucc) := of_eq (PureSyntaxTrace.closed_rename w S Fin.castSucc) (under hs M)
  have hR := BinaryUnionSyntax.includes_left _ _ _ hu1
  have hS := BinaryUnionSyntax.includes_right _ _ _ hu1
  apply Derives.disjE (BinaryUnionSyntax.member_cases _ _ _ _ hu1 (.hyp (Or.inl rfl)))
  · exact HornTraceMonotone.step PureSyntaxRules.rules _ _ _ _ (add hR _)
      (PureSyntaxTrace.closed_at _ _ _ (add hr1 _) (.hyp (Or.inl rfl)))
  · exact HornTraceMonotone.step PureSyntaxRules.rules _ _ _ _ (add hS _)
      (PureSyntaxTrace.closed_at _ _ _ (add hs1 _) (.hyp (Or.inl rfl)))

theorem join_witness {m} {Γ : Context m} (w r s R S U : Fin m)
    (hu : Derives Γ (BinaryUnionSyntax.joined U R S))
    (hr : Derives Γ (PureSyntaxTrace.witness w r R)) (hs : Derives Γ (PureSyntaxTrace.witness w s S)) :
    Derives Γ (pairWitness w r s U) :=
  .conjI (BinaryUnionSyntax.subset _ _ _ _ hu (.conjL hr) (.conjL hs))
    (.conjI (join_closed _ _ _ _ hu (.conjR (.conjR hr)) (.conjR (.conjR hs)))
      (.conjI (BinaryUnionSyntax.member_left _ _ _ _ hu (.conjL (.conjR hr)))
        (BinaryUnionSyntax.member_right _ _ _ _ hu (.conjL (.conjR hs)))))

theorem two_conditions {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s : Fin m)
    (hr : Derives Γ (PureSyntaxTrace.condition w r)) (hs : Derives Γ (PureSyntaxTrace.condition w s)) :
    Derives Γ (pairCondition w r s) := by
  let R := PureSyntaxTrace.witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hs1 : Derives Δ (PureSyntaxTrace.condition w.castSucc s.castSucc) := of_eq (PureSyntaxTrace.condition_rename w s Fin.castSucc) (under hs R)
  let S := PureSyntaxTrace.witness w.castSucc.castSucc s.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) hs1
  have hR1 : Derives Ξ (PureSyntaxTrace.witness w.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc) := of_eq (PureSyntaxTrace.witness_rename _ _ _ Fin.castSucc) (under hR S)
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  let U := BinaryUnionSyntax.joined (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
  let Θ := Context.add U (Context.image Formula.raise Ξ)
  apply Derives.exE (p := U) (BinaryUnionSyntax.exists_joined (ZFContext.under (ZFContext.under hZ R) S) (Fin.last m).castSucc (Fin.last (m+1)))
  have hR2 : Derives Θ (PureSyntaxTrace.witness w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := of_eq (PureSyntaxTrace.witness_rename _ _ _ Fin.castSucc) (under hR1 U)
  have hS1 : Derives Θ (PureSyntaxTrace.witness w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (PureSyntaxTrace.witness_rename _ _ _ Fin.castSucc) (under hS U)
  have hU : Derives Θ U := .hyp (Or.inl rfl)
  have hp := join_witness _ _ _ _ _ _ hU hR2 hS1
  have he : Derives Θ (pairCondition w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2))
    exact of_eq (by simp only [Formula.instantiate, pairWitness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hp
  exact of_eq (by simp only [Formula.raise, pairCondition_rename]) he

end PPAC.Migration.Internal.PureSyntaxTraceMerge
