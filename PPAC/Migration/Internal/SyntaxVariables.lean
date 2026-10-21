import PPAC.Migration.Internal.SyntaxVariableSyntax

/-! 全部内部自然索引的真实bvar/fvar编码存在唯一；两类编码在对象核内互斥。 -/
namespace PPAC.Migration.Internal.SyntaxVariables
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForestSyntax SyntaxNodeSyntax SyntaxVariableSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (existsCode bound w i) := by
  have hs := SyntaxNodes.exists_node hZ 0 w i Fin.elim0 hw hi (.eqRefl w)
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (scalar w.castSucc i.castSucc (Fin.last m))
  let Ξ := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hs
  apply Derives.exE (p := S) hs
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ S
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw S
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hin : Derives Ξ (inputs 1 w.castSucc (fun _ => Fin.last m)) := .conjI (.conjL hS) (.eqRefl _)
  have hn := SyntaxConstructors.exists_constructor hZ1 1 (tag bound) _ _ hw1 hin
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (constructor 1 (tag bound) w.castSucc.castSucc (fun _ => (Fin.last m).castSucc) (Fin.last (m+1)))
  let Δ := Context.add N (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hs2 : Derives Δ (scalar w.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := by simpa only [S, Formula.raise, scalar_rename] using under (Derives.conjR hS) N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hc := intro_code bound _ _ _ _ hs2 (.conjR hN)
  have hout : Derives Δ (existsCode bound w.castSucc.castSucc i.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simp only [Formula.instantiate, Formula.rename, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hN) hc
  simpa only [Formula.raise, existsCode_rename] using hout

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w i n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (code bound w i n)) (hr : Derives Γ (code bound w i r)) : Derives Γ (.equal n r) := by
  let N := codeBody bound w i n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_code bound w i n _ hn
  have hr1 : Derives Ξ (code bound w.castSucc i.castSucc r.castSucc) := by simpa only [Formula.raise, code_rename] using under hr N
  let R := codeBody bound w.castSucc i.castSucc r.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_code bound w.castSucc i.castSucc r.castSucc _ hr1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ N) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw N) R
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hN2 : Derives Δ ((scalar w.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).conj
      (constructor 1 (tag bound) w.castSucc.castSucc (fun _ => (Fin.last m).castSucc) n.castSucc.castSucc)) := by
    simpa only [N, codeBody, Formula.raise, Formula.rename, scalar_rename, constructor_rename] using under hN R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have heq := SyntaxNodes.unique hZ2 0 _ _ Fin.elim0 _ _ hw2 (.conjL hN2) (.conjL hR)
  have hc := unary_subst _ _ _ _ _ (eq_symm heq) (.conjR hR)
  exact SyntaxConstructors.unique hZ2 1 (tag bound) _ _ _ _ hw2 (.conjR hN2) hc

theorem disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i j n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (code true w i n)) (hr : Derives Γ (code false w j n)) : Derives Γ .bot := by
  let N := codeBody true w i n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_code true w i n _ hn
  have hr1 : Derives Ξ (code false w.castSucc j.castSucc n.castSucc) := by simpa only [Formula.raise, code_rename] using under hr N
  let R := codeBody false w.castSucc j.castSucc n.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_code false w.castSucc j.castSucc n.castSucc _ hr1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ N) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw N) R
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hN2 : Derives Δ ((scalar w.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).conj
      (constructor 1 0 w.castSucc.castSucc (fun _ => (Fin.last m).castSucc) n.castSucc.castSucc)) := by
    simpa only [N, codeBody, tag, ite_true, Formula.raise, Formula.rename, scalar_rename, constructor_rename] using under hN R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint hZ2 1 1 0 1 (by decide) _ _ _ _ hw2 (.conjR hN2) (.conjR hR)

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (fiber bound w i) := by
  have he := exists_code hZ bound w i hw hi
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (code bound w.castSucc i.castSucc (Fin.last m))
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  change Derives Γ (.ex E) at he
  apply Derives.exE (p := E) he
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ E
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((code bound w.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let R := code bound w.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add R (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 R
    have hn2 : Derives Δ (code bound w.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [E, Formula.raise, code_rename] using under (Derives.conjR hE) R
    exact unique (ZFContext.under hZ1 R) bound _ _ _ _ hw2 (.hyp (Or.inl rfl)) hn2
  have hout : Derives Ξ (fiber bound w.castSucc i.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hE hu
  simpa only [Formula.raise, fiber_rename] using hout
end PPAC.Migration.Internal.SyntaxVariables
