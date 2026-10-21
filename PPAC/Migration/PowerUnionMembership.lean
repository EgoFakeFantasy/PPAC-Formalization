import PPAC.Migration.HierarchyMemberSyntax

/-! 幂集并算子的精确成员公式；正反向均消去实际集合见证。 -/
namespace PPAC.Migration.PowerUnionMembership
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax PowerSetSyntax
open InsertSyntax PowerUnionSyntax HierarchyMemberSyntax

theorem value_member {m} {Γ : Context m} (a h b w z : Fin m)
    (hb : Derives Γ (.mem b a)) (hv : Derives Γ (PowerValueSyntax.value h b w))
    (hz : Derives Γ (.mem z w)) : Derives Γ (graphMember a h z) := by
  let V := (edge h.castSucc b.castSucc (Fin.last m)).conj (powerOf w.castSucc (Fin.last m))
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hbV : Derives Ξ (.mem b.castSucc a.castSucc) := under hb V
  have hzV : Derives Ξ (.mem z.castSucc w.castSucc) := under hz V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have hs := Derives.impE (.conjL (power_at w.castSucc (Fin.last m) z.castSucc (.conjR hV))) hzV
  simpa only [Formula.raise, graphMember_rename] using intro_graphMember a.castSucc h.castSucc z.castSucc
    b.castSucc (Fin.last m) (.conjI hbV (.conjI (.conjL hV) hs))

theorem image_member {m} {Γ : Context m} (a h w z : Fin m)
    (hi : Derives Γ (PowerValueSyntax.image a h w)) (hz : Derives Γ (.mem z w)) :
    Derives Γ (graphMember a h z) := by
  let B := (Formula.mem (Fin.last m) a.castSucc).conj
    (PowerValueSyntax.value h.castSucc (Fin.last m) w.castSucc)
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hi
  apply Derives.exE (p := B) hi
  have hzB : Derives Ξ (.mem z.castSucc w.castSucc) := under hz B
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  simpa only [Formula.raise, graphMember_rename] using value_member a.castSucc h.castSucc (Fin.last m)
    w.castSucc z.castSucc (.conjL hB) (.conjR hB) hzB

theorem range_union_member {m} {Γ : Context m} (c a h y z : Fin m)
    (hr : Derives Γ (PowerValueSyntax.range c a h)) (hu : Derives Γ (unionOf y c))
    (hz : Derives Γ (.mem z y)) : Derives Γ (graphMember a h z) := by
  have hx := Derives.impE (.conjL (union_at y c z hu)) hz
  let W := (Formula.mem (Fin.last m) c.castSucc).conj (.mem z.castSucc (Fin.last m))
  let Ξ := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at hx
  apply Derives.exE (p := W) hx
  have hrW : Derives Ξ (PowerValueSyntax.range c.castSucc a.castSucc h.castSucc) := by
    simpa only [Formula.raise, PowerValueSyntax.range_rename] using under hr W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hi := Derives.impE (.conjL (PowerValueSyntax.range_at c.castSucc a.castSucc h.castSucc (Fin.last m) hrW)) (.conjL hW)
  simpa only [Formula.raise, graphMember_rename] using image_member a.castSucc h.castSucc (Fin.last m) z.castSucc hi (.conjR hW)

theorem range_union_point {m} {Γ : Context m} (c a h y z b v : Fin m)
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0))
    (hr : Derives Γ (PowerValueSyntax.range c a h)) (hu : Derives Γ (unionOf y c))
    (hb : Derives Γ (.mem b a)) (he : Derives Γ (edge h b v)) (hs : Derives Γ (subset z v)) :
    Derives Γ (.mem z y) := by
  have hx := power_instance v hp
  let P := powerOf (Fin.last m) v.castSucc
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hx
  apply Derives.exE (p := P) hx
  have hrP : Derives Ξ (PowerValueSyntax.range c.castSucc a.castSucc h.castSucc) := by
    simpa only [Formula.raise, PowerValueSyntax.range_rename] using under hr P
  have huP : Derives Ξ (unionOf y.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu P
  have hbP : Derives Ξ (.mem b.castSucc a.castSucc) := under hb P
  have heP : Derives Ξ (edge h.castSucc b.castSucc v.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under he P
  have hsP : Derives Ξ (subset z.castSucc v.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hs P
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hvalue := PowerValueSyntax.intro_value h.castSucc b.castSucc v.castSucc (Fin.last m) heP hP
  have hi : Derives Ξ (PowerValueSyntax.image a.castSucc h.castSucc (Fin.last m)) := by
    apply Derives.exI b.castSucc
    simp only [Formula.instantiate, Formula.rename, PowerValueSyntax.value_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hbP hvalue
  have hc := Derives.impE (.conjR (PowerValueSyntax.range_at c.castSucc a.castSucc h.castSucc (Fin.last m) hrP)) hi
  have hz := Derives.impE (.conjR (power_at (Fin.last m) v.castSucc z.castSucc hP)) hsP
  exact .impE (.conjR (union_at y.castSucc c.castSucc z.castSucc huP))
    (InsertLogic.fiber_intro c.castSucc z.castSucc (Fin.last m) hc hz)

theorem range_union_back {m} {Γ : Context m} (c a h y z : Fin m)
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0))
    (hr : Derives Γ (PowerValueSyntax.range c a h)) (hu : Derives Γ (unionOf y c))
    (hz : Derives Γ (graphMember a h z)) : Derives Γ (.mem z y) := by
  let W := graphMemberWitnesses a h z
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_graphMember a h z _ hz
  have hpW : Derives Ξ (Source.SetLanguage.powerSet.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hp W
  have hrW : Derives Ξ (PowerValueSyntax.range c.castSucc.castSucc a.castSucc.castSucc h.castSucc.castSucc) := by
    simpa only [Formula.raise, PowerValueSyntax.range_rename] using OrderedPairElimination.under_two hr W
  have huW : Derives Ξ (unionOf y.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using OrderedPairElimination.under_two hu W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  exact range_union_point c.castSucc.castSucc a.castSucc.castSucc h.castSucc.castSucc y.castSucc.castSucc z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hpW hrW huW (.conjL hW) (.conjL (.conjR hW)) (.conjR (.conjR hW))

theorem operation_forward {m} {Γ : Context m} (a h y z : Fin m)
    (hop : Derives Γ (operation a h y)) (hz : Derives Γ (.mem z y)) : Derives Γ (graphMember a h z) := by
  let C := (PowerValueSyntax.range (Fin.last m) a.castSucc h.castSucc).conj (unionOf y.castSucc (Fin.last m))
  let Ξ := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hop
  apply Derives.exE (p := C) hop
  have hzC : Derives Ξ (.mem z.castSucc y.castSucc) := under hz C
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  simpa only [Formula.raise, graphMember_rename] using range_union_member (Fin.last m) a.castSucc h.castSucc y.castSucc z.castSucc
    (.conjL hC) (.conjR hC) hzC

theorem operation_backward {m} {Γ : Context m} (a h y z : Fin m)
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0))
    (hop : Derives Γ (operation a h y)) (hz : Derives Γ (graphMember a h z)) : Derives Γ (.mem z y) := by
  let C := (PowerValueSyntax.range (Fin.last m) a.castSucc h.castSucc).conj (unionOf y.castSucc (Fin.last m))
  let Ξ := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hop
  apply Derives.exE (p := C) hop
  have hpC : Derives Ξ (Source.SetLanguage.powerSet.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp C
  have hzC : Derives Ξ (graphMember a.castSucc h.castSucc z.castSucc) := by
    simpa only [Formula.raise, graphMember_rename] using under hz C
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  exact range_union_back (Fin.last m) a.castSucc h.castSucc y.castSucc z.castSucc hpC (.conjL hC) (.conjR hC) hzC

theorem operation_iff {m} {Γ : Context m} (a h y z : Fin m)
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0)) (hop : Derives Γ (operation a h y)) :
    Derives Γ ((Formula.mem z y).iff (graphMember a h z)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact operation_forward a h y z (add hop _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact operation_backward a h y z (add hp _) (add hop _) (.hyp (Or.inl rfl))
end PPAC.Migration.PowerUnionMembership
