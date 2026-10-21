import PPAC.Migration.Internal.SyntaxTreeValiditySyntax

/-! 原节点树有效性由全部真实子字段有效性推出；完整图覆盖全部内部边。 -/
namespace PPAC.Migration.Internal.SyntaxTreeValidity
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxNodeSyntax SyntaxPositionSyntax
open SyntaxForestFields (graphLaw graphLaw_rename)
open SyntaxTreeValiditySyntax StructuralTreeValiditySyntax FormulaCodeShapeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem graph_children {m} {Γ : Context m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (g : Fin m)
    (hg : Derives Γ (graphLaw k xs g)) (hv : Derives Γ (validInputs k w xs)) :
    Derives Γ (validChildren w g) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hg2 : Derives Δ (graphLaw k (fun j => (xs j).castSucc.castSucc) g.castSucc.castSucc) := by
    simpa only [Formula.raise, graphLaw_rename] using OrderedPairElimination.under_two hg E
  have hv2 : Derives Δ (validInputs k w.castSucc.castSucc (fun j => (xs j).castSucc.castSucc)) := by
    simpa only [Formula.raise, validInputs_rename] using OrderedPairElimination.under_two hv E
  have hpos := Derives.impE (.conjL (SyntaxForestFields.law_at k (fun j => (xs j).castSucc.castSucc)
    g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hg2)) (.hyp (Or.inl rfl))
  have hh : Derives Δ ((positions k (fun j => (xs j).castSucc.castSucc) (Fin.last m).castSucc (Fin.last (m+1))).imp
      (valid w.castSucc.castSucc (Fin.last (m+1)))) := by
    apply positions_imp
    intro j
    apply Derives.impI
    have hp : Derives (Context.add
        ((SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc).conj (.equal (Fin.last (m+1)) (xs j).castSucc.castSucc)) Δ)
        ((SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc).conj (.equal (Fin.last (m+1)) (xs j).castSucc.castSucc)) :=
      .hyp (Or.inl rfl)
    exact valid_subst _ _ _ (eq_symm (.conjR hp)) (add (inputs_at k _ _ j hv2) _)
  exact .impE hh hpos

theorem node {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w a : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNodeSyntax.node k w a xs n))
    (hv : Derives Γ (validInputs k w xs)) : Derives Γ (valid w n) := by
  have he := FormulaCodeShape.from_node hZ k w a xs n hw hn
  let B := (shapeBody w n).conj
    (uniqueShape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
      (Fin.last (m+2)).castSucc (Fin.last (m+3)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_fiber w n _ he
  have hZ4 := StructuralListLengthSyntax.zf_under_four hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using StructuralListLengthSyntax.under_four hw B
  have hn4 : Derives Δ (SyntaxNodeSyntax.node k w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc
      (fun j => (xs j).castSucc.castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, node_rename] using StructuralListLengthSyntax.under_four hn B
  have hv4 : Derives Δ (validInputs k w.castSucc.castSucc.castSucc.castSucc (fun j => (xs j).castSucc.castSucc.castSucc.castSucc)) := by
    simpa only [Formula.raise, validInputs_rename] using StructuralListLengthSyntax.under_four hv B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg := SyntaxNodeFields.node hZ4 k w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc
    (fun j => (xs j).castSucc.castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 hn4 (.conjL hB)
  have hc := graph_children k _ _ _ hg hv4
  have hr := intro_recursive _ _ _ _ _ _ (.conjI (.conjL hB) hc)
  have hout := StructuralTreeDecode.recursive_to_valid hZ4 _ _ hw4 hr
  simpa only [Formula.raise, valid_rename] using hout

theorem constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs n))
    (hv : Derives Γ (validInputs k w xs)) : Derives Γ (valid w n) := by
  let C := constructorBody k tag w xs n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_constructor k tag w xs n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hv1 : Derives Δ (validInputs k w.castSucc (fun j => (xs j).castSucc)) := by
    simpa only [Formula.raise, validInputs_rename] using under hv C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := node (ZFContext.under hZ C) k w.castSucc (Fin.last m) (fun j => (xs j).castSucc) n.castSucc hw1 (.conjR hC) hv1
  simpa only [Formula.raise, valid_rename] using hout

theorem scalar {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (SyntaxNodeSyntax.scalar w i n)) : Derives Γ (valid w n) :=
  node hZ 0 w i Fin.elim0 n hw hs (.eqRefl w)
end PPAC.Migration.Internal.SyntaxTreeValidity
