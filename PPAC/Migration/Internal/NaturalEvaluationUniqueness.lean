import PPAC.Migration.Internal.NaturalEvaluationExistence

/-! 实际唯一原递归图与后继域唯一性推出全部内部自然位置的唯一末值。 -/
namespace PPAC.Migration.Internal.NaturalEvaluationUniqueness
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax OrdinalSyntax ReplacementPredicates
open NaturalRecursionSyntax NaturalEvaluationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem recursor_domain_subst {n m} {Γ : Context m} (q : Formula (n+3)) (τ : Fin n → Fin m) (f d e : Fin m)
    (he : Derives Γ (.equal d e)) (hf : Derives Γ (OrdinalRecursionSyntax.recursor q τ f d)) :
    Derives Γ (OrdinalRecursionSyntax.recursor q τ f e) := by
  have hi : Derives Γ ((OrdinalRecursionSyntax.recursor q (paramsUp τ) f.castSucc (Fin.last m)).instantiate d) := by
    simpa only [Formula.instantiate, OrdinalRecursionSyntax.recursor_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf
  have hout := Derives.eqSubst (OrdinalRecursionSyntax.recursor q (paramsUp τ) f.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, OrdinalRecursionSyntax.recursor_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hout

theorem edge_graph_subst {m} {Γ : Context m} (f g r y : Fin m)
    (he : Derives Γ (.equal f g)) (hf : Derives Γ (edge f r y)) : Derives Γ (edge g r y) := by
  have hi : Derives Γ ((edge (Fin.last m) r.castSucc y.castSucc).instantiate f) := by
    simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf
  have hout := Derives.eqSubst (edge (Fin.last m) r.castSucc y.castSucc) he hi
  simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hout

theorem recursors_equal {n m} {Γ : Context m} (q : Formula (n+3)) (τ : Fin n → Fin m) (d f g : Fin m)
    (hall : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique q τ)) (hd : Derives Γ (ordinal d))
    (hf : Derives Γ (OrdinalRecursionSyntax.recursor q τ f d)) (hg : Derives Γ (OrdinalRecursionSyntax.recursor q τ g d)) :
    Derives Γ (.equal f g) := by
  have hk := NaturalEvaluationExistence.fiber_at q τ d hall hd
  let K := (OrdinalRecursionSyntax.recursor q (paramsUp τ) (Fin.last m) d.castSucc).conj
    (OrdinalRecursionExistenceSyntax.uniqueAt q (paramsUp τ) d.castSucc (Fin.last m))
  let Ξ := Context.add K (Context.image Formula.raise Γ)
  change Derives Γ (.ex K) at hk
  apply Derives.exE (p := K) hk
  have hfK : Derives Ξ (OrdinalRecursionSyntax.recursor q (paramsUp τ) f.castSucc d.castSucc) := by
    simpa only [Formula.raise, OrdinalRecursionSyntax.recursor_rename, paramsUp] using under hf K
  have hgK : Derives Ξ (OrdinalRecursionSyntax.recursor q (paramsUp τ) g.castSucc d.castSucc) := by
    simpa only [Formula.raise, OrdinalRecursionSyntax.recursor_rename, paramsUp] using under hg K
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have hfi := Derives.allE f.castSucc (.conjR hK)
  have hgi := Derives.allE g.castSucc (.conjR hK)
  have hfi' : Derives Ξ ((OrdinalRecursionSyntax.recursor q (paramsUp τ) f.castSucc d.castSucc).imp (.equal f.castSucc (Fin.last m))) := by
    simpa only [Formula.instantiate, Formula.rename, OrdinalRecursionSyntax.recursor_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hfi
  have hgi' : Derives Ξ ((OrdinalRecursionSyntax.recursor q (paramsUp τ) g.castSucc d.castSucc).imp (.equal g.castSucc (Fin.last m))) := by
    simpa only [Formula.instantiate, Formula.rename, OrdinalRecursionSyntax.recursor_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hgi
  exact eq_trans (.impE hfi' hfK) (eq_symm (.impE hgi' hgK))

theorem traces_value_unique {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r d e f g y z : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hall : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend ρ w a))) (hd : Derives Γ (ordinal d))
    (hf : Derives Γ (trace p ρ w a r d f)) (hg : Derives Γ (trace p ρ w a r e g))
    (hy : Derives Γ (edge f r y)) (hz : Derives Γ (edge g r z)) : Derives Γ (.equal y z) := by
  have hed := OmegaUniversal.successor_unique e d r he (.conjL hg) (.conjL hf)
  have hg' := recursor_domain_subst (matrix p) (extend ρ w a) g e d hed (.conjR hg)
  have hfg := recursors_equal (matrix p) (extend ρ w a) d f g hall hd (.conjR hf) hg'
  have hz' := edge_graph_subst g f r z (eq_symm hfg) hz
  exact GraphProperties.single_valued f d r y z he (.conjL (.conjR hf)) hy hz'

theorem evaluation_unique {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r y z : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w))
    (hord : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (ordinal (Fin.last m)))))
    (hall : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend ρ w a)))
    (hy : Derives Γ (evaluation p ρ w a r y)) (hz : Derives Γ (evaluation p ρ w a r z)) : Derives Γ (.equal y z) := by
  let Y := witness p ρ w a r y
  let Γy := Context.add Y (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_evaluation p ρ w a r y _ hy
  have heY : Derives Γy (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two he Y
  have hwY : Derives Γy (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw Y
  have hrY : Derives Γy (.mem r.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two hr Y
  have hordY : Derives Γy (.all ((Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).imp (ordinal (Fin.last (m+2))))) := by
    simpa only [Formula.raise, Formula.rename, ordinal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc] using OrderedPairElimination.under_two hord Y
  have hallY : Derives Γy (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc)) := by
    simpa only [Formula.raise, OrdinalRecursionExistenceSyntax.allUnique_rename, extend_rename, paramsUp] using OrderedPairElimination.under_two hall Y
  have hzY : Derives Γy (evaluation p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc z.castSucc.castSucc) := by
    simpa only [Formula.raise, evaluation_rename, paramsUp] using OrderedPairElimination.under_two hz Y
  have hY : Derives Γy Y := .hyp (Or.inl rfl)
  have hdW := OmegaStructureAlgebra.successor_member w.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc heY hwY hrY (.conjL (.conjL hY))
  have hdOrd := OmegaOrdinals.at_member w.castSucc.castSucc (Fin.last m).castSucc hordY hdW
  let Z := witness p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc z.castSucc.castSucc
  let Ξ := Context.add Z (Context.image Formula.raise (Context.image Formula.raise Γy))
  apply eliminate_evaluation p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc z.castSucc.castSucc _ hzY
  have heZ : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two heY Z
  have hallZ : Derives Ξ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend (paramsUp (paramsUp (paramsUp (paramsUp ρ))))
      w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc)) := by
    simpa only [Formula.raise, OrdinalRecursionExistenceSyntax.allUnique_rename, extend_rename, paramsUp] using OrderedPairElimination.under_two hallY Z
  have hdOrdZ : Derives Ξ (ordinal (Fin.last m).castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two hdOrd Z
  have hfZ : Derives Ξ (trace p (paramsUp (paramsUp (paramsUp (paramsUp ρ)))) w.castSucc.castSucc.castSucc.castSucc
      a.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) := by
    simpa only [Formula.raise, trace_rename, paramsUp] using OrderedPairElimination.under_two (.conjL hY) Z
  have hyZ : Derives Ξ (edge (Fin.last (m+1)).castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, edge_rename] using OrderedPairElimination.under_two (.conjR hY) Z
  have hZ : Derives Ξ Z := .hyp (Or.inl rfl)
  exact traces_value_unique p (paramsUp (paramsUp (paramsUp (paramsUp ρ)))) w.castSucc.castSucc.castSucc.castSucc
    a.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3))
    y.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc heZ hallZ hdOrdZ hfZ (.conjL hZ) hyZ (.conjR hZ)
end PPAC.Migration.Internal.NaturalEvaluationUniqueness
