import PPAC.Migration.Internal.PacketDivisionValueSyntax

/-! Existence and uniqueness for every internal natural output, with invalid outputs retained. -/
namespace PPAC.Migration.Internal.PacketDivisionValue
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketDivisionSyntax PacketDivisionValueSyntax
open PacketAffineSyntax PacketAffineCore
open SyntaxRenameQuerySyntax (of_eq)

theorem range {m} {Γ : Context m} (w B n : Fin m) (hd : Derives Γ (decomposes w B n)) : Derives Γ (.mem n w) := by
  let C := decompositionBody w B n
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ hd
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact output_guard (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) (old 2 n) hC

theorem decomposes_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ ((decomposes w B n).iff (.mem n w)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact range w B n (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact PacketDivisionInduction.exists_decomposition (ZFContext.add hZ _) wide w B n (add hw _) (add hB _) (.hyp (Or.inl rfl))

theorem unique_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n d q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) : Derives Γ (uniquePair w B n d q) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := affine (old 2 w : Fin (m+2)) (old 2 B) (slot 2 0) (slot 2 1) (old 2 n)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw H)
  have ha2 := of_eq (affine_rename w B d q n (old 2)) (HornBinderRules.under_body 2 ha H)
  exact PacketDivisionUnique.unique (HornBinderRules.zf_body 2 hZ H) (old 2 w) (old 2 B)
    (slot 2 0) (slot 2 1) (old 2 d) (old 2 q) (old 2 n) hw2 (.hyp (Or.inl rfl)) ha2

theorem exists_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hn : Derives Γ (.mem n w)) : Derives Γ (PacketDivisionValueSyntax.fiber w B n) := by
  have he := PacketDivisionInduction.exists_decomposition hZ wide w B n hw hB hn
  let C := decompositionBody w B n
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ he
  have hZ2 := HornBinderRules.zf_body 2 hZ C
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hu := unique_pair hZ2 (old 2 w) (old 2 B) (old 2 n) (slot 2 0) (slot 2 1) hw2 hC
  exact of_eq (fiber_rename w B n (old 2)).symm
    (intro_fiber (old 2 w) (old 2 B) (old 2 n) (slot 2 0) (slot 2 1) hC hu)

theorem fiber_range {m} {Γ : Context m} (w B n : Fin m) (hf : Derives Γ (PacketDivisionValueSyntax.fiber w B n)) : Derives Γ (.mem n w) := by
  let C := fiberBody w B n
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ hf
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact output_guard (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) (old 2 n) (.conjL hC)

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ ((PacketDivisionValueSyntax.fiber w B n).iff (.mem n w)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact fiber_range w B n (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact exists_fiber (ZFContext.add hZ _) wide w B n (add hw _) (add hB _) (.hyp (Or.inl rfl))

theorem accepted_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hn : Derives Γ (.mem n w)) : Derives Γ (acceptedDecomposition wide w n) := by
  have he := PacketDivisionInduction.exists_decomposition hZ wide w B n hw hB hn
  let C := decompositionBody w B n
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ he
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw C)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 2)) (HornBinderRules.under_body 2 hB C)
  have hA : Derives Δ C := .hyp (Or.inl rfl)
  have hc := Derives.impE (.conjR (PacketAffineAccepted.accepted_iff (HornBinderRules.zf_body 2 hZ C) wide
    (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) (old 2 n) hw2 hB2)) hA
  exact of_eq (acceptedDecomposition_rename wide w n (old 2)).symm
    (intro_accepted wide (old 2 w) (old 2 n) (slot 2 0) (slot 2 1) hc)

theorem accepted_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (acceptedDecomposition wide w n)) : Derives Γ (.mem n w) := by
  let C := acceptedBody wide w n
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ ha
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw C)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 2)) (HornBinderRules.under_body 2 hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hA := Derives.impE (.conjL (PacketAffineAccepted.accepted_iff (HornBinderRules.zf_body 2 hZ C) wide
    (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) (old 2 n) hw2 hB2)) hC
  exact output_guard (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) (old 2 n) hA

theorem accepted_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ ((acceptedDecomposition wide w n).iff (.mem n w)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact accepted_range (ZFContext.add hZ _) wide w B n (add hw _) (add hB _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact accepted_exists (ZFContext.add hZ _) wide w B n (add hw _) (add hB _) (.hyp (Or.inl rfl))

theorem accepted_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d q e p n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted wide w d q n))
    (hb : Derives Γ (PacketAffineAcceptedSyntax.accepted wide w e p n)) : Derives Γ ((Formula.equal d e).conj (.equal q p)) :=
  PacketDivisionUnique.unique hZ w B d q e p n hw
    (.impE (.conjL (PacketAffineAccepted.accepted_iff hZ wide w B d q n hw hB)) ha)
    (.impE (.conjL (PacketAffineAccepted.accepted_iff hZ wide w B e p n hw hB)) hb)

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (allLaw w B) := by
  apply Derives.allI
  exact fiber_iff (HornBinderRules.zf_many 1 hZ) wide w.castSucc B.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (HornBinderRules.under_many 1 hw))
    (of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (HornBinderRules.under_many 1 hB))

theorem all_accepted_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (allAcceptedLaw wide w) := by
  apply Derives.allI
  exact accepted_iff (HornBinderRules.zf_many 1 hZ) wide w.castSucc B.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (HornBinderRules.under_many 1 hw))
    (of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (HornBinderRules.under_many 1 hB))

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsSystem wide w) := by
  let P := PacketAffineLiteralSyntax.frame wide w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ (PacketAffineRuleData.radix wide) w hw)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hZ1 := ZFContext.under hZ P
  have hs : Derives Δ (system wide w.castSucc (Fin.last m)) := .conjI hP
    (.conjI (all_law hZ1 wide w.castSucc (Fin.last m) hw1 (.conjR hP))
      (all_accepted_law hZ1 wide w.castSucc (Fin.last m) hw1 (.conjR hP)))
  have he : Derives Δ (existsSystem wide w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, system_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hs
  exact of_eq (existsSystem_rename wide w Fin.castSucc).symm he

end PPAC.Migration.Internal.PacketDivisionValue
