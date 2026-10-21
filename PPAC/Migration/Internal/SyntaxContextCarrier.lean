import PPAC.Migration.Internal.SyntaxContextCarrierSyntax

/-! 原PowerSet实际构造上下文载体；每个内部Kuratowski上下文对及其状态子集均有真实集合界。 -/
namespace PPAC.Migration.Internal.SyntaxContextCarrier
open Source SourceAlgebra SourceLogic OmegaSyntax PairSyntax PowerSetSyntax RestrictionSyntax SyntaxContextCarrierSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem pair_subset {m} {Γ : Context m} (p x y w : Fin m) (hp : Derives Γ (pair p x y))
    (hx : Derives Γ (.mem x w)) (hy : Derives Γ (.mem y w)) : Derives Γ (subset p w) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) p.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hp1 : Derives Δ (pair p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, pair_rename] using under hp M
  apply Derives.disjE (UnorderedPairLogic.member_cases _ _ _ _ hp1 (.hyp (Or.inl rfl)))
  · exact mem_subst (eq_symm (.hyp (Or.inl rfl))) (add (under hx M) _)
  · exact mem_subst (eq_symm (.hyp (Or.inl rfl))) (add (under hy M) _)

theorem ordered_member {m} {Γ : Context m} (w a c b f p : Fin m)
    (ha : Derives Γ (powerOf a w)) (hc : Derives Γ (powerOf c a))
    (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w)) (hp : Derives Γ (ordered p b f)) : Derives Γ (.mem p c) := by
  let B := OrderedPairElimination.witnesses p b f
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply OrderedPairElimination.eliminate p b f _ hp
  have ha1 : Derives Δ (powerOf a.castSucc.castSucc w.castSucc.castSucc) := by
    simpa only [Formula.raise, powerOf_rename] using OrderedPairElimination.under_two ha B
  have hc1 : Derives Δ (powerOf c.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, powerOf_rename] using OrderedPairElimination.under_two hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hsSub := pair_subset _ _ _ _ (.conjL hB) (OrderedPairElimination.under_two hb B) (OrderedPairElimination.under_two hb B)
  have htSub := pair_subset _ _ _ _ (.conjL (.conjR hB)) (OrderedPairElimination.under_two hb B) (OrderedPairElimination.under_two hf B)
  have hs := Derives.impE (.conjR (power_at _ _ _ ha1)) hsSub
  have ht := Derives.impE (.conjR (power_at _ _ _ ha1)) htSub
  have hpSub := pair_subset _ _ _ _ (.conjR (.conjR hB)) hs ht
  exact .impE (.conjR (power_at _ _ _ hc1)) hpSub

theorem pair_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c b f : Fin m)
    (ha : Derives Γ (powerOf a w)) (hc : Derives Γ (powerOf c a))
    (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w)) : Derives Γ (pairExistsIn c b f) := by
  have he := OrderedPairExistence.exists_pair b f (ZFContext.arithmetic hZ).base.pairing
  let P := ordered (Fin.last m) b.castSucc f.castSucc
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have ha1 : Derives Δ (powerOf a.castSucc w.castSucc) := by simpa only [Formula.raise, powerOf_rename] using under ha P
  have hc1 : Derives Δ (powerOf c.castSucc a.castSucc) := by simpa only [Formula.raise, powerOf_rename] using under hc P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hm := ordered_member _ _ _ _ _ _ ha1 hc1 (under hb P) (under hf P) hP
  have hout : Derives Δ (pairExistsIn c.castSucc b.castSucc f.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, ordered_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hm hP
  simpa only [Formula.raise, pairExistsIn_rename] using hout

theorem state_member {m} {Γ : Context m} (c u v : Fin m) (hu : Derives Γ (powerOf u c))
    (hv : Derives Γ (subset v c)) : Derives Γ (.mem v u) := .impE (.conjR (power_at u c v hu)) hv

theorem exists_tower {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) : Derives Γ (existsTower w) := by
  have hpower : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0) :=
    .hyp (hZ _ ⟨_, Source.SetLanguage.IsZFAxiom.powerSet, rfl⟩)
  have heA := power_instance w hpower
  let A := powerOf (Fin.last m) w.castSucc
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  apply Derives.exE (p := A) heA
  have hpower1 : Derives Ξ (Source.SetLanguage.powerSet.rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hpower A
  have heC := power_instance (Fin.last m) hpower1
  let C := powerOf (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply Derives.exE (p := C) heC
  have hpower2 : Derives Δ (Source.SetLanguage.powerSet.rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hpower1 C
  have heU := power_instance (Fin.last (m+1)) hpower2
  let U := powerOf (Fin.last (m+2)) (Fin.last (m+1)).castSucc
  let Θ := Context.add U (Context.image Formula.raise Δ)
  apply Derives.exE (p := U) heU
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hA3 : Derives Θ (powerOf (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc) := by
    simpa only [A, Formula.raise, powerOf_rename] using under (under hA C) U
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hC3 : Derives Θ (powerOf (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc) := by
    simpa only [C, Formula.raise, powerOf_rename] using under hC U
  have hU : Derives Θ U := .hyp (Or.inl rfl)
  have hout : Derives Θ (existsTower w.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc.castSucc
    apply Derives.exI (Fin.last (m+1)).castSucc
    apply Derives.exI (Fin.last (m+2))
    simp only [Formula.instantiate, tower_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hA3 (.conjI hC3 hU)
  simpa only [Formula.raise, existsTower_rename] using hout

theorem tower_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c u a' c' u' : Fin m)
    (ht : Derives Γ (tower w a c u)) (ht' : Derives Γ (tower w a' c' u')) :
    Derives Γ ((Formula.equal a a').conj ((Formula.equal c c').conj (.equal u u'))) := by
  have he := (ZFContext.arithmetic hZ).base.extensionality
  have ha := PowerSetLogic.unique a a' w he (.conjL ht) (.conjL ht')
  have hc' := PowerSetLogic.subst_base c' a' a (eq_symm ha) (.conjL (.conjR ht'))
  have hc := PowerSetLogic.unique c c' a he (.conjL (.conjR ht)) hc'
  have hu' := PowerSetLogic.subst_base u' c' c (eq_symm hc) (.conjR (.conjR ht'))
  exact .conjI ha (.conjI hc (PowerSetLogic.unique u u' c he (.conjR (.conjR ht)) hu'))
end PPAC.Migration.Internal.SyntaxContextCarrier
