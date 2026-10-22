import PPAC.Migration.Internal.SyntaxIndexLiftSyntax

/-! 提升关系在真实零/后继上的全部内部点性质；原域和值域界由原图恢复。 -/
namespace PPAC.Migration.Internal.SyntaxIndexLiftPoint
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxIndexMapSyntax SyntaxIndexLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def output {m} (r k y : Fin m) : Formula m := .ex
  ((edge r.castSucc k.castSucc (Fin.last m)).conj (successor y.castSucc (Fin.last m)))

theorem output_rename {m n} (r k y : Fin m) (ρ : Fin m → Fin n) :
    (output r k y).rename ρ = output (ρ r) (ρ k) (ρ y) := by
  simp only [output, Formula.rename, edge_rename, successor_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem shifted_empty_conflict {m} {Γ : Context m} (r a x y : Fin m)
    (hx : Derives Γ (empty x)) (hv : Derives Γ (shifted r a x y)) : Derives Γ .bot := by
  let B := shiftBody r a x y
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_shifted r a x y _ hv
  have hx2 : Derives Δ (empty x.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using OrderedPairElimination.under_two hx B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .impE (OmegaStructureAlgebra.successor_not_empty _ _ (.conjL (.conjR hB))) hx2

theorem zero_output {m} {Γ : Context m} (r a x y : Fin m)
    (hx : Derives Γ (empty x)) (hv : Derives Γ (value r a x y)) : Derives Γ (empty y) := by
  apply Derives.disjE hv
  · exact .conjR (.hyp (Or.inl rfl))
  · exact .botE (shifted_empty_conflict r a x y (add hx _) (.hyp (Or.inl rfl)))

theorem at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a x y k : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (.mem k w)) (hx : Derives Γ (successor x k))
    (hv : Derives Γ (value r a x y)) : Derives Γ ((Formula.mem k a).conj (output r k y)) := by
  apply Derives.disjE hv
  · exact .botE (.impE (add (OmegaStructureAlgebra.successor_not_empty x k hx) _) (.conjL (.hyp (Or.inl rfl))))
  · let V := shifted r a x y
    let B := shiftBody r a x y
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add V Γ)))
    apply eliminate_shifted r a x y _ (.hyp (Or.inl rfl))
    have hZ2 := ZFContext.under_two (ZFContext.add hZ V) B
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
      simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two (add hw V) B
    have hx2 : Derives Δ (successor x.castSucc.castSucc k.castSucc.castSucc) := by
      simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two (add hx V) B
    have hk2 : Derives Δ (.mem k.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two (add hk V) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hkeq := SyntaxIndexLiftOrder.successor_injective hZ2 _ _ _ _ hw2 hk2 hx2 (.conjL (.conjR hB))
    have he := IterationValues.edge_subst_input r.castSucc.castSucc (Fin.last m).castSucc k.castSucc.castSucc
      (Fin.last (m+1)) (eq_symm hkeq) (.conjR (.conjL hB))
    have ho : Derives Δ (output r.castSucc.castSucc k.castSucc.castSucc y.castSucc.castSucc) := by
      apply Derives.exI (Fin.last (m+1))
      simp only [Formula.instantiate, Formula.rename, edge_rename, successor_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      exact .conjI he (.conjR (.conjR hB))
    have hm := mem_subst (eq_symm hkeq) (.conjL (.conjL hB))
    simpa only [Formula.raise, Formula.rename, output_rename] using Derives.conjI hm ho

theorem source_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a u x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hu : Derives Γ (successor u a))
    (hv : Derives Γ (value r a x y)) : Derives Γ (.mem x u) := by
  apply Derives.disjE hv
  · exact SyntaxIndexLiftOrder.zero_member (ZFContext.add hZ _) w a u x (add hw _) (add ha _) (add hu _) (.conjL (.hyp (Or.inl rfl)))
  · let V := shifted r a x y
    let B := shiftBody r a x y
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add V Γ)))
    apply eliminate_shifted r a x y _ (.hyp (Or.inl rfl))
    have hZ2 := ZFContext.under_two (ZFContext.add hZ V) B
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two (add hw V) B
    have hu2 : Derives Δ (successor u.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two (add hu V) B
    have ha2 : Derives Δ (.mem a.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two (add ha V) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hkNat := StructuralListTraceOrder.member_member hZ2 _ _ _ hw2 ha2 (.conjL (.conjL hB))
    exact SyntaxIndexLiftOrder.successor_member hZ2 _ _ _ _ _ hw2 hkNat ha2
      (.conjL (.conjL hB)) (.conjL (.conjR hB)) hu2

theorem target_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c v x y : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c)) (hv : Derives Γ (successor v c))
    (hh : Derives Γ (value r a x y)) : Derives Γ (.mem y v) := by
  apply Derives.disjE hh
  · exact SyntaxIndexLiftOrder.zero_member (ZFContext.add hZ _) w c v y (add hw _) (add (.conjR (.conjL hm)) _) (add hv _) (.conjR (.hyp (Or.inl rfl)))
  · let V := shifted r a x y
    let B := shiftBody r a x y
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add V Γ)))
    apply eliminate_shifted r a x y _ (.hyp (Or.inl rfl))
    have hZ2 := ZFContext.under_two (ZFContext.add hZ V) B
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two (add hw V) B
    have hv2 : Derives Δ (successor v.castSucc.castSucc c.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two (add hv V) B
    have hm2 : Derives Δ (indexMap w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := by
      simpa only [Formula.raise, indexMap_rename] using OrderedPairElimination.under_two (add hm V) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hl := edge_target _ _ _ _ _ _ hm2 (.conjR (.conjL hB))
    have hcNat := Derives.conjR (.conjL hm2)
    have hlNat := StructuralListTraceOrder.member_member hZ2 _ _ _ hw2 hcNat hl
    exact SyntaxIndexLiftOrder.successor_member hZ2 _ _ _ _ _ hw2 hlNat hcNat hl (.conjR (.conjR hB)) hv2
end PPAC.Migration.Internal.SyntaxIndexLiftPoint
