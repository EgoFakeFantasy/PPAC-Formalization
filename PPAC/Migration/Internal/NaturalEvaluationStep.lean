import PPAC.Migration.Internal.NaturalEvaluationRange
import PPAC.Migration.OrdinalRecursionRestriction

/-! 实际前缀递归图把两次独立末值求值接成同一后继方程。 -/
namespace PPAC.Migration.Internal.NaturalEvaluationStep
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax OrdinalSyntax ReplacementPredicates
open NaturalRecursionSyntax NaturalEvaluationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem successor_subset {m} {Γ : Context m} (d s : Fin m) (hs : Derives Γ (successor d s)) :
    Derives Γ (RestrictionSyntax.subset s d) := by
  apply Derives.allI
  have hs' : Derives (Context.image Formula.raise Γ) (successor d.castSucc s.castSucc) := by
    simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc hs
  apply Derives.impI
  exact InsertLogic.old_member d.castSucc s.castSucc s.castSucc (Fin.last m) (add hs' _) (.hyp (Or.inl rfl))

theorem recursor_step {n m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ)
    (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r s d f u v : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hsd : Derives Γ (.mem s d)) (hsub : Derives Γ (RestrictionSyntax.subset s d))
    (hf : Derives Γ (OrdinalRecursionSyntax.recursor (matrix p) (extend ρ w a) f d))
    (hu : Derives Γ (edge f r u)) (hv : Derives Γ (edge f s v)) : Derives Γ (rel p ρ u v) := by
  have hh := Derives.impE (Derives.impE (OrdinalRecursionSyntax.equations_at (matrix p) (extend ρ w a) f d s v (.conjR hf)) hsd) hv
  let H := (RestrictionSyntax.restrict (Fin.last m) f.castSucc s.castSucc).conj
    (OrdinalRecursionSyntax.operator (matrix p) (paramsUp (extend ρ w a)) s.castSucc (Fin.last m) v.castSucc)
  let Ξ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have hAH := ArithmeticContext.under hA H
  have hwH : Derives Ξ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw H
  have hrH : Derives Ξ (.mem r.castSucc w.castSucc) := under hr H
  have hsH : Derives Ξ (successor s.castSucc r.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hs H
  have hsubH : Derives Ξ (RestrictionSyntax.subset s.castSucc d.castSucc) := by
    simpa only [Formula.raise, RestrictionSyntax.subset_rename] using under hsub H
  have hfH : Derives Ξ (functionOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under (.conjL hf) H
  have huH : Derives Ξ (edge f.castSucc r.castSucc u.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hu H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have hfn := RestrictionFunction.function_restrict (Fin.last m) f.castSucc d.castSucc s.castSucc hfH hsubH (.conjL hH)
  have he := RestrictionEdges.restricted_edge (Fin.last m) f.castSucc s.castSucc r.castSucc u.castSucc (.conjL hH) huH
    (InsertLogic.new_member s.castSucc r.castSucc r.castSucc hsH)
  have hop : Derives Ξ (operation p (paramsUp ρ) w.castSucc a.castSucc s.castSucc (Fin.last m) v.castSucc) := by
    simpa only [extend_up, matrix_operator] using Derives.conjR hH
  simpa only [Formula.raise, rel_rename, paramsUp] using NaturalRecursionLaws.operation_successor hAH.base p (paramsUp ρ)
    w.castSucc a.castSucc s.castSucc r.castSucc (Fin.last m) u.castSucc v.castSucc hAH.transitiveSeparation hwH hrH hsH hfn he hop

theorem prefix_evaluation {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r s d f y : Fin m)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (hsOrd : Derives Γ (ordinal s)) (hsub : Derives Γ (RestrictionSyntax.subset s d))
    (hf : Derives Γ (OrdinalRecursionSyntax.recursor (matrix p) (extend ρ w a) f d))
    (hs : Derives Γ (successor s r)) (hy : Derives Γ (edge f r y)) : Derives Γ (evaluation p ρ w a r y) := by
  have hg := OrdinalRecursionRestriction.exists_restricted (matrix p) (extend ρ w a) f s d hsep (.conjL hsOrd) hsub hf
  let G := (RestrictionSyntax.restrict (Fin.last m) f.castSucc s.castSucc).conj
    (OrdinalRecursionSyntax.recursor (matrix p) (extend (paramsUp ρ) w.castSucc a.castSucc) (Fin.last m) s.castSucc)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  simp only [OrdinalRecursionRestriction.restrictedExists, extend_up] at hg
  change Derives Γ (.ex G) at hg
  apply Derives.exE (p := G) hg
  have hsG : Derives Ξ (successor s.castSucc r.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hs G
  have hyG : Derives Ξ (edge f.castSucc r.castSucc y.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hy G
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have he := RestrictionEdges.restricted_edge (Fin.last m) f.castSucc s.castSucc r.castSucc y.castSucc (.conjL hG) hyG
    (InsertLogic.new_member s.castSucc r.castSucc r.castSucc hsG)
  have ht : Derives Ξ (trace p (paramsUp ρ) w.castSucc a.castSucc r.castSucc s.castSucc (Fin.last m)) := .conjI hsG (.conjR hG)
  simpa only [Formula.raise, evaluation_rename, paramsUp] using intro_evaluation p (paramsUp ρ)
    w.castSucc a.castSucc r.castSucc y.castSucc s.castSucc (Fin.last m) ht he

theorem trace_step {n m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ)
    (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r s d f u v : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hord : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (ordinal (Fin.last m)))))
    (hall : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend ρ w a)))
    (hu : Derives Γ (evaluation p ρ w a r u)) (hf : Derives Γ (trace p ρ w a s d f))
    (hv : Derives Γ (edge f s v)) : Derives Γ (rel p ρ u v) := by
  have hsW := OmegaStructureAlgebra.successor_member w s r hA.base.extensionality hw hr hs
  have hsOrd := OmegaOrdinals.at_member w s hord hsW
  have hsub := successor_subset d s (.conjL hf)
  have hrd := InsertLogic.old_member d s s r (.conjL hf) (InsertLogic.new_member s r r hs)
  have ht := GraphProperties.output_exists f d r (.conjL (.conjR hf)) hrd
  let T := edge f.castSucc r.castSucc (Fin.last m)
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hAT := ArithmeticContext.under hA T
  have hwT : Derives Ξ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw T
  have hrT : Derives Ξ (.mem r.castSucc w.castSucc) := under hr T
  have hsT : Derives Ξ (successor s.castSucc r.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hs T
  have hsOrdT : Derives Ξ (ordinal s.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under hsOrd T
  have hsubT : Derives Ξ (RestrictionSyntax.subset s.castSucc d.castSucc) := by
    simpa only [Formula.raise, RestrictionSyntax.subset_rename] using under hsub T
  have hordT : Derives Ξ (.all ((Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).imp (ordinal (Fin.last (m+1))))) := by
    simpa only [Formula.raise, Formula.rename, ordinal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc] using under hord T
  have hallT : Derives Ξ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend (paramsUp ρ) w.castSucc a.castSucc)) := by
    simpa only [Formula.raise, OrdinalRecursionExistenceSyntax.allUnique_rename, extend_rename, paramsUp] using under hall T
  have huT : Derives Ξ (evaluation p (paramsUp ρ) w.castSucc a.castSucc r.castSucc u.castSucc) := by
    simpa only [Formula.raise, evaluation_rename, paramsUp] using under hu T
  have hfT : Derives Ξ (trace p (paramsUp ρ) w.castSucc a.castSucc s.castSucc d.castSucc f.castSucc) := by
    simpa only [Formula.raise, trace_rename, paramsUp] using under hf T
  have hvT : Derives Ξ (edge f.castSucc s.castSucc v.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hv T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have heval := prefix_evaluation p (paramsUp ρ) w.castSucc a.castSucc r.castSucc s.castSucc d.castSucc f.castSucc (Fin.last m)
    hAT.restrictionSeparation hsOrdT hsubT (.conjR hfT) hsT hT
  have heq := NaturalEvaluationUniqueness.evaluation_unique p (paramsUp ρ) w.castSucc a.castSucc r.castSucc u.castSucc (Fin.last m)
    hAT.base.extensionality hwT hrT hordT hallT huT heval
  have hrel := recursor_step hAT p (paramsUp ρ) w.castSucc a.castSucc r.castSucc s.castSucc d.castSucc f.castSucc (Fin.last m) v.castSucc
    hwT hrT hsT (InsertLogic.new_member d.castSucc s.castSucc s.castSucc (.conjL hfT)) hsubT (.conjR hfT) hT hvT
  simpa only [Formula.raise, rel_rename, paramsUp] using
    CheckedSequence.rel_subst_left p (paramsUp ρ) (Fin.last m) u.castSucc v.castSucc (eq_symm heq) hrel

theorem evaluation_step {n m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ)
    (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r s u v : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hord : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (ordinal (Fin.last m)))))
    (hall : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend ρ w a)))
    (hu : Derives Γ (evaluation p ρ w a r u)) (hv : Derives Γ (evaluation p ρ w a s v)) : Derives Γ (rel p ρ u v) := by
  let V := witness p ρ w a s v
  let Ξ := Context.add V (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_evaluation p ρ w a s v _ hv
  have hAV := ArithmeticContext.under_two hA V
  have hwV : Derives Ξ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw V
  have hrV : Derives Ξ (.mem r.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two hr V
  have hsV : Derives Ξ (successor s.castSucc.castSucc r.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two hs V
  have hordV : Derives Ξ (.all ((Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).imp (ordinal (Fin.last (m+2))))) := by
    simpa only [Formula.raise, Formula.rename, ordinal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc] using OrderedPairElimination.under_two hord V
  have hallV : Derives Ξ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc)) := by
    simpa only [Formula.raise, OrdinalRecursionExistenceSyntax.allUnique_rename, extend_rename, paramsUp] using OrderedPairElimination.under_two hall V
  have huV : Derives Ξ (evaluation p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc u.castSucc.castSucc) := by
    simpa only [Formula.raise, evaluation_rename, paramsUp] using OrderedPairElimination.under_two hu V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  simpa only [Formula.raise, rel_rename, paramsUp] using trace_step hAV p (paramsUp (paramsUp ρ))
    w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    u.castSucc.castSucc v.castSucc.castSucc hwV hrV hsV hordV hallV huV (.conjL hV) (.conjR hV)
end PPAC.Migration.Internal.NaturalEvaluationStep
