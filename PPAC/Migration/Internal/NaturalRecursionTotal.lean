import PPAC.Migration.Internal.NaturalRecursionSyntax
import PPAC.Migration.SourcePropositional

/-! 总步进关系给任意实际前段图上的真实输出；不存在正确历史或宿主选择函数输入。 -/
namespace PPAC.Migration.Internal.NaturalRecursionTotal
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalRecursionSyntax

theorem pred_intro {m} {Γ : Context m} (w x t : Fin m)
    (ht : Derives Γ (.mem t w)) (hs : Derives Γ (successor x t)) :
    Derives Γ (OmegaStructureSyntax.predecessor w x) := by
  apply Derives.exI t
  simp only [Formula.instantiate, Formula.rename, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ht hs

theorem pred_of_step {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x h y : Fin m)
    (hs : Derives Γ (stepAt p ρ w x h y)) : Derives Γ (OmegaStructureSyntax.predecessor w x) := by
  let W := stepWitness p ρ w x h y
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_step p ρ w x h y _ hs
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hout := pred_intro w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (.conjL (.conjL hW)) (.conjR (.conjL hW))
  simpa only [Formula.raise, OmegaStructureSyntax.predecessor_rename] using hout

theorem intro_value {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h y : Fin m)
    (hy : Derives Γ (operation p ρ w a x h y)) : Derives Γ (hasOperation p ρ w a x h) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, operation_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy

theorem value_at_predecessor {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h t : Fin m)
    (ht : Derives Γ (.mem t w)) (hs : Derives Γ (successor x t))
    (hf : Derives Γ (functionOn h x)) (hTotal : Derives Γ (relationTotal p ρ)) :
    Derives Γ (hasOperation p ρ w a x h) := by
  have htx := InsertLogic.new_member x t t hs
  have hu := GraphProperties.output_exists h x t hf htx
  let U := edge h.castSucc t.castSucc (Fin.last m)
  let Γu := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hu
  apply Derives.exE (p := U) hu
  have htU : Derives Γu (.mem t.castSucc w.castSucc) := under ht U
  have hsU : Derives Γu (successor x.castSucc t.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hs U
  have hTotalU : Derives Γu (relationTotal p (paramsUp ρ)) := by
    simpa only [Formula.raise, relationTotal_rename, paramsUp] using under hTotal U
  have hU : Derives Γu U := .hyp (Or.inl rfl)
  have hv := total_at p (paramsUp ρ) (Fin.last m) hTotalU
  let V := rel p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add V (Context.image Formula.raise Γu)
  change Derives Γu (.ex V) at hv
  apply Derives.exE (p := V) hv
  have htV : Derives Ξ (.mem t.castSucc.castSucc w.castSucc.castSucc) := under htU V
  have hsV : Derives Ξ (successor x.castSucc.castSucc t.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hsU V
  have hUV : Derives Ξ (edge h.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, U, edge_rename] using under hU V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have hop : Derives Ξ (operation p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc
      x.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1))) :=
    .disjL (intro_step p (paramsUp (paramsUp ρ)) w.castSucc.castSucc x.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1))
      t.castSucc.castSucc (Fin.last m).castSucc htV hsV hUV hV)
  have hout := intro_value p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc x.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1)) hop
  simpa only [Formula.raise, hasOperation_rename, paramsUp] using hout

theorem exists_operation {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h : Fin m)
    (hf : Derives Γ (functionOn h x)) (hTotal : Derives Γ (relationTotal p ρ)) :
    Derives Γ (hasOperation p ρ w a x h) := by
  apply SourcePropositional.by_cases (OmegaStructureSyntax.predecessor w x) (hasOperation p ρ w a x h)
  · let P := OmegaStructureSyntax.predecessor w x
    let Γp := Context.add P Γ
    have hP : Derives Γp P := .hyp (Or.inl rfl)
    let T := (Formula.mem (Fin.last m) w.castSucc).conj (successor x.castSucc (Fin.last m))
    let Ξ := Context.add T (Context.image Formula.raise Γp)
    change Derives Γp (.ex T) at hP
    apply Derives.exE (p := T) hP
    have hfT : Derives Ξ (functionOn h.castSucc x.castSucc) := by
      simpa only [Formula.raise, functionOn_rename] using under (add hf P) T
    have hTotalT : Derives Ξ (relationTotal p (paramsUp ρ)) := by
      simpa only [Formula.raise, relationTotal_rename, paramsUp] using under (add hTotal P) T
    have hT : Derives Ξ T := .hyp (Or.inl rfl)
    simpa only [Formula.raise, hasOperation_rename, paramsUp] using
      value_at_predecessor p (paramsUp ρ) w.castSucc a.castSucc x.castSucc h.castSucc (Fin.last m) (.conjL hT) (.conjR hT) hfT hTotalT
  · apply intro_value p ρ w a x h a
    exact .disjR (.conjI (.hyp (Or.inl rfl)) (.eqRefl a))

theorem operator_total {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a : Fin m)
    (ht : Derives Γ (relationTotal p ρ)) :
    Derives Γ (OrdinalRecursionTotal.total (matrix p) (extend ρ w a)) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have ht' : Derives Δ (relationTotal p (paramsUp (paramsUp ρ))) := by
    simpa only [Formula.raise, relationTotal_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ht)
  apply Derives.impI
  let M := (OrdinalSyntax.ordinal (Fin.last m).castSucc).conj (functionOn (Fin.last (m+1)) (Fin.last m).castSucc)
  have hM : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
  simpa only [OrdinalRecursionTotal.hasValue, extend_up, matrix_operator, hasOperation] using
    exists_operation p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjR hM) (add ht' M)
end PPAC.Migration.Internal.NaturalRecursionTotal
