import PPAC.Migration.Internal.SyntaxIndexLift

/-! 实际binder提升图在全部内部候选、零和真实后继上的精确边刻画。 -/
namespace PPAC.Migration.Internal.SyntaxIndexLiftEdges
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxIndexMapSyntax SyntaxIndexLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def valueLaw {m} (r a g : Fin m) : Formula m := .all (.all
  ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    (value r.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

theorem valueLaw_rename {m n} (r a g : Fin m) (ρ : Fin m → Fin n) :
    (valueLaw r a g).rename ρ = valueLaw (ρ r) (ρ a) (ρ g) := by
  simp only [valueLaw, Formula.iff, Formula.rename, edge_rename, value_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem all_edges {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c u v g : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (lifted w r a c u v g)) : Derives Γ (valueLaw r a g) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  have hh2 : Derives Δ (lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc
      u.castSucc.castSucc v.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, lifted_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hh)
  exact SyntaxIndexLift.edge_iff (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc)
    _ _ _ _ _ _ _ (Fin.last m).castSucc (Fin.last (m+1)) hw2 hh2

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c u v g z y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (lifted w r a c u v g)) (hz : Derives Γ (empty z)) :
    Derives Γ ((edge g z y).iff (empty y)) := by
  have he := SyntaxIndexLift.edge_iff hZ w r a c u v g z y hw hh
  apply Derives.conjI
  · apply Derives.impI
    have hv := Derives.impE (add (.conjL he) (edge g z y)) (.hyp (Or.inl rfl))
    exact SyntaxIndexLiftPoint.zero_output r a z y (add hz _) hv
  · apply Derives.impI
    exact .impE (add (.conjR he) _) (.disjL (.conjI (add hz _) (.hyp (Or.inl rfl))))

theorem successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c u v g i j k l : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (lifted w r a c u v g))
    (hk : Derives Γ (.mem k a)) (hi : Derives Γ (successor i k)) (hj : Derives Γ (successor j l)) :
    Derives Γ ((edge g i j).iff (edge r k l)) := by
  have he := SyntaxIndexLift.edge_iff hZ w r a c u v g i j hw hh
  apply Derives.conjI
  · apply Derives.impI
    let E := edge g i j
    let Ξ := Context.add E Γ
    have hv := Derives.impE (add (.conjL he) E) (.hyp (Or.inl rfl))
    have hkNat := StructuralListTraceOrder.member_member (ZFContext.add hZ E) w k a
      (add hw E) (add (.conjL (.conjL (.conjL hh))) E) (add hk E)
    have hd := SyntaxIndexLiftPoint.at_successor (ZFContext.add hZ E) w r a i j k (add hw E) hkNat (add hi E) hv
    let T := (edge r.castSucc k.castSucc (Fin.last m)).conj (successor j.castSucc (Fin.last m))
    let Δ := Context.add T (Context.image Formula.raise Ξ)
    have hx : Derives Ξ (.ex T) := .conjR hd
    apply Derives.exE hx
    have hZ1 := ZFContext.under (ZFContext.add hZ E) T
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw E) T
    have hm1 : Derives Δ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := by
      simpa only [Formula.raise, indexMap_rename] using under (add (Derives.conjL hh) E) T
    have hj1 : Derives Δ (successor j.castSucc l.castSucc) := by simpa only [Formula.raise, successor_rename] using under (add hj E) T
    have hT : Derives Δ T := .hyp (Or.inl rfl)
    have htC := edge_target _ _ _ _ _ _ hm1 (.conjL hT)
    have htNat := StructuralListTraceOrder.member_member hZ1 _ _ _ hw1 (.conjR (.conjL hm1)) htC
    have hEq := SyntaxIndexLiftOrder.successor_injective hZ1 _ _ _ _ hw1 htNat (.conjR hT) hj1
    have ho := GraphPointwiseSyntax.edge_subst_output _ _ _ _ hEq (.conjL hT)
    simpa only [Formula.raise, edge_rename] using ho
  · apply Derives.impI
    have hv := intro_shifted r a i j k l (add hk (edge r k l)) (.hyp (Or.inl rfl)) (add hi _) (add hj _)
    exact .impE (add (.conjR he) _) (.disjR hv)
end PPAC.Migration.Internal.SyntaxIndexLiftEdges
