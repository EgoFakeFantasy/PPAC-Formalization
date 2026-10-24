import PPAC.Migration.Internal.ProjectSubsetSyntax

/-! Exact output typing and all-candidate functionality of the subset template. -/
namespace PPAC.Migration.Internal.ProjectSubsetPoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectSubsetSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix


theorem inputs2_subst {m} {Γ : Context m} (tag : Nat) (w x y X Y n : Fin m)
    (hx : Derives Γ (.equal x X)) (hy : Derives Γ (.equal y Y))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two x y) n)) :
    Derives Γ (SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two X Y) n) := by
  let P0 := SyntaxNodeSyntax.constructor 2 tag w.castSucc (SyntaxAtomSyntax.two (Fin.last m) y.castSucc) n.castSucc
  have h0a : P0.instantiate x = SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two x y) n := by
    simp only [P0, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h0b : P0.instantiate X = SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two X y) n := by
    simp only [P0, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hc0 := of_eq h0b (Derives.eqSubst P0 hx (of_eq h0a.symm hc))
  let P1 := SyntaxNodeSyntax.constructor 2 tag w.castSucc (SyntaxAtomSyntax.two X.castSucc (Fin.last m)) n.castSucc
  have h1a : P1.instantiate y = SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two X y) n := by
    simp only [P1, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1b : P1.instantiate Y = SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two X Y) n := by
    simp only [P1, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hc1 := of_eq h1b (Derives.eqSubst P1 hy (of_eq h1a.symm hc0))
  exact hc1

theorem inputs3_subst {m} {Γ : Context m} (tag : Nat) (w s x y S X Y n : Fin m)
    (hs : Derives Γ (.equal s S)) (hx : Derives Γ (.equal x X)) (hy : Derives Γ (.equal y Y))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 3 tag w (SyntaxAtomSyntax.three s x y) n)) :
    Derives Γ (SyntaxNodeSyntax.constructor 3 tag w (SyntaxAtomSyntax.three S X Y) n) := by
  let P0 := SyntaxNodeSyntax.constructor 3 tag w.castSucc (SyntaxAtomSyntax.three (Fin.last m) x.castSucc y.castSucc) n.castSucc
  have h0a : P0.instantiate s = SyntaxNodeSyntax.constructor 3 tag w (SyntaxAtomSyntax.three s x y) n := by
    simp only [P0, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h0b : P0.instantiate S = SyntaxNodeSyntax.constructor 3 tag w (SyntaxAtomSyntax.three S x y) n := by
    simp only [P0, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hc0 := of_eq h0b (Derives.eqSubst P0 hs (of_eq h0a.symm hc))
  let P1 := SyntaxNodeSyntax.constructor 3 tag w.castSucc (SyntaxAtomSyntax.three S.castSucc (Fin.last m) y.castSucc) n.castSucc
  have h1a : P1.instantiate x = SyntaxNodeSyntax.constructor 3 tag w (SyntaxAtomSyntax.three S x y) n := by
    simp only [P1, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1b : P1.instantiate X = SyntaxNodeSyntax.constructor 3 tag w (SyntaxAtomSyntax.three S X y) n := by
    simp only [P1, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hc1 := of_eq h1b (Derives.eqSubst P1 hx (of_eq h1a.symm hc0))
  let P2 := SyntaxNodeSyntax.constructor 3 tag w.castSucc (SyntaxAtomSyntax.three S.castSucc X.castSucc (Fin.last m)) n.castSucc
  have h2a : P2.instantiate y = SyntaxNodeSyntax.constructor 3 tag w (SyntaxAtomSyntax.three S X y) n := by
    simp only [P2, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h2b : P2.instantiate Y = SyntaxNodeSyntax.constructor 3 tag w (SyntaxAtomSyntax.three S X Y) n := by
    simp only [P2, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hc2 := of_eq h2b (Derives.eqSubst P2 hy (of_eq h2a.symm hc1))
  exact hc2

theorem matrix_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z x y q r : Fin m)
    (e f : Fin 8 → Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (matrix w b z x y q e)) (hf : Derives Γ (matrix w b z x y r f)) : Derives Γ (.equal q r) := by
  have hX := ProjectBoundShiftLaws.unique hZ w x (e 1) (f 1) hw (.conjL (.conjR he)) (.conjL (.conjR hf))
  have hY := ProjectBoundShiftLaws.unique hZ w y (e 2) (f 2) hw (.conjL (.conjR (.conjR he))) (.conjL (.conjR (.conjR hf)))
  have hV := SyntaxVariables.unique hZ true w z (e 3) (f 3) hw (.conjL (.conjR (.conjR (.conjR he)))) (.conjL (.conjR (.conjR (.conjR hf))))
  have hS := SyntaxConstructors.unique hZ 0 0 w Fin.elim0 (e 4) (f 4) hw (.conjL (.conjR (.conjR (.conjR (.conjR he))))) (.conjL (.conjR (.conjR (.conjR (.conjR hf)))))
  have hL0 := inputs3_subst 2 w (e 4) (e 3) (e 1) (f 4) (f 3) (f 1) (e 5) hS hV hX (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR he))))))
  have hL := SyntaxConstructors.unique hZ 3 2 w (SyntaxAtomSyntax.three (f 4) (f 3) (f 1)) (e 5) (f 5) hw hL0 (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hf))))))
  have hR0 := inputs3_subst 2 w (e 4) (e 3) (e 2) (f 4) (f 3) (f 2) (e 6) hS hV hY (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR he)))))))
  have hR := SyntaxConstructors.unique hZ 3 2 w (SyntaxAtomSyntax.three (f 4) (f 3) (f 2)) (e 6) (f 6) hw hR0 (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hf)))))))
  have hP0 := inputs2_subst 7 w (e 5) (e 6) (f 5) (f 6) (e 7) hL hR (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR he))))))))
  have hP := SyntaxConstructors.unique hZ 2 7 w (SyntaxAtomSyntax.two (f 5) (f 6)) (e 7) (f 7) hw hP0 (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hf))))))))
  have hQ0 := SyntaxVariableSyntax.unary_subst 9 w (e 7) (f 7) q hP (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR he))))))))
  exact SyntaxConstructors.unique hZ 1 9 w (fun _ => f 7) q r hw hQ0 (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hf))))))))

theorem matrix_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z x y q : Fin m)
    (env : Fin 8 → Fin m) (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w))
    (hz : Derives Γ (empty z)) (hx : Derives Γ (SyntaxTermSyntax.branch true w b x))
    (hy : Derives Γ (SyntaxTermSyntax.branch true w b y)) (hm : Derives Γ (matrix w b z x y q env)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q b z) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hB := Derives.conjL hm
  have hBW := OmegaStructureAlgebra.successor_member w (env 0) b (ZFContext.arithmetic hZ).base.extensionality hw hb hB
  have hX := ProjectBoundShiftLaws.target_type hZ w b (env 0) z x (env 1) hw hb hzW hB hx (.conjL (.conjR hm))
  have hY := ProjectBoundShiftLaws.target_type hZ w b (env 0) z y (env 2) hw hb hzW hB hy (.conjL (.conjR (.conjR hm)))
  have hzB := SyntaxIndexLiftOrder.zero_member hZ w b (env 0) z hw hb hB hz
  have hV := SyntaxTermSyntax.intro_term true w (env 0) z (env 3) z (.conjI (.conjI hBW hzW) hzB) (.conjL (.conjR (.conjR (.conjR hm))))
  have hL := Derives.impE (.conjR (FormulaCodeKnownAtomic.member_iff hZ w (env 0) z (env 4) (env 3) (env 1) (env 5) hw (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hm)))))))) (.conjI (.conjL (.conjR (.conjR (.conjR (.conjR hm))))) (.conjI hV hX))
  have hR := Derives.impE (.conjR (FormulaCodeKnownAtomic.member_iff hZ w (env 0) z (env 4) (env 3) (env 2) (env 6) hw (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hm))))))))) (.conjI (.conjL (.conjR (.conjR (.conjR (.conjR hm))))) (.conjI hV hY))
  have hP := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w (env 0) z (env 5) (env 6) (env 7) hw (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hm)))))))))) (.conjI (.conjI hBW hzW) (.conjI hL hR))
  have ha := Derives.impE (.conjR (FormulaCodeBranchSyntax.at_successor hZ w (env 7) b z (env 0) hB)) hP
  exact Derives.impE (.conjR (FormulaCodeKnownLogical.forall_iff hZ w b z (env 7) q hw (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hm)))))))))) (.conjI (.conjI hb hzW) ha)

end PPAC.Migration.Internal.ProjectSubsetPoint
