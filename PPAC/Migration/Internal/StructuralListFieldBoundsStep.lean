import PPAC.Migration.Internal.StructuralListFieldBoundsSyntax

/-! 原Cons零字段使用头界，后继字段使用尾归纳界及原自然数传递性。 -/
namespace PPAC.Migration.Internal.StructuralListFieldBoundsStep
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListFieldSyntax StructuralListFieldBoundsSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem member_trans {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w y t n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hy : Derives Γ (.mem y t)) (ht : Derives Γ (.mem t n)) : Derives Γ (.mem y n) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  exact .impE (.impE (OrdinalSyntax.transitiveSet_at n t y (.conjL ho)) ht) hy

theorem cons_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s h t n i y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hc : Derives Γ (consCode w h t n))
    (hl : Derives Γ (hasLength w t r)) (hp : Derives Γ (property w r)) (hi : Derives Γ (.mem i s))
    (hy : Derives Γ (field w n i y)) : Derives Γ (.mem y n) := by
  have hsW := OmegaStructureAlgebra.successor_member w s r (ZFContext.arithmetic hZ).base.extensionality hw hr hs
  have hiW := StructuralListTraceOrder.member_member hZ w i s hw hsW hi
  have hd := OmegaStructureAlgebra.decomposition_at w i
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hiW
  have hbounds := StructuralConsCore.components hZ w h t n hw hh ht hc
  apply Derives.disjE hd
  · have he := StructuralListFieldCons.zero_point (ZFContext.add hZ _) _ _ _ _ _ _
      (add hw _) (add hh _) (add ht _) (add hc _) (.hyp (Or.inl rfl)) (add hy _)
    exact mem_subst (eq_symm he) (add (.conjL hbounds) _)
  · let P := OmegaStructureSyntax.predecessor w i
    let Γp := Context.add P Γ
    let J := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add J (Context.image Formula.raise Γp)
    have hj : Derives Γp (.ex J) := .hyp (Or.inl rfl)
    apply Derives.exE (p := J) hj
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ P) J
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise := under (add hp P) J
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
    have hc1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc n.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hc
    have hl1 : Derives Δ (hasLength w.castSucc t.castSucc r.castSucc) := by simpa only [Formula.raise, hasLength_rename] using lift hl
    have hp1 : Derives Δ (property w.castSucc r.castSucc) := by simpa only [Formula.raise, property_rename] using lift hp
    have hy1 : Derives Δ (field w.castSucc n.castSucc i.castSucc y.castSucc) := by simpa only [Formula.raise, field_rename] using lift hy
    have hJ : Derives Δ J := .hyp (Or.inl rfl)
    have hjR := StructuralListSuffixArithmetic.predecessor_inside hZ1 _ _ _ _ _ hw1 (lift hr) hs1 (.conjR hJ) (lift hi)
    have hyT := StructuralListFieldCons.successor_forward hZ1 _ _ _ _ _ _ _ hw1 (lift hh) (lift ht) (.conjL hJ) (.conjR hJ) hc1 hy1
    have hyBound := at_field _ _ _ _ _ hp1 hl1 hjR hyT
    exact member_trans hZ1 _ _ _ _ hw1 (StructuralConsCore.range hZ1 _ _ _ _ hw1 hc1) hyBound (lift (.conjR hbounds))

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s n i y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hp : Derives Γ (property w r)) (hl : Derives Γ (hasLength w n s)) (hi : Derives Γ (.mem i s))
    (hy : Derives Γ (field w n i y)) : Derives Γ (.mem y n) := by
  have hv := StructuralListCodeLength.successor_view hZ w n r s hw hr hs hl
  let C := StructuralListCodeSyntax.consViewBody w n r
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListCodeSyntax.eliminate_view w n r _ hv
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ C
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise := OrderedPairElimination.under_two hp C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hs2 : Derives Δ (successor s.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hp2 : Derives Δ (property w.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hp
  have hy2 : Derives Δ (field w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc) := by simpa only [Formula.raise, field_rename] using lift hy
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have htW := StructuralListLengthBasic.code_member _ _ _ (.conjR (.conjL hC))
  exact cons_point hZ2 _ _ _ _ _ _ _ _ hw2 (lift hr) hs2 (.conjL (.conjL hC)) htW (.conjR hC) (.conjR (.conjL hC)) hp2 (lift hi) hy2

theorem property_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hp : Derives Γ (property w r)) : Derives Γ (property w s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let L := hasLength w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc s.castSucc.castSucc.castSucc
  let M := Formula.mem (Fin.last (m+1)).castSucc s.castSucc.castSucc.castSucc
  let F := field w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
  let Δ := Context.add F (Context.add M (Context.add L (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))
  have hZ3 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) L) M) F
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise.raise := add (add (add (OrdinalRestriction.raise_three hp) L) M) F
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hs3 : Derives Δ (successor s.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hp3 : Derives Δ (property w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hp
  exact point hZ3 _ _ _ _ _ _ hw3 (lift hr) hs3 hp3 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralListFieldBoundsStep
