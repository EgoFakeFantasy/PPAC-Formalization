import PPAC.Migration.Internal.SyntaxNodes

/-! 所有有限标签/字段构造器实际存在唯一，异标签互斥，全部子字段严格小于原父码。 -/
namespace PPAC.Migration.Internal.SyntaxConstructors
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForestSyntax SyntaxNumeralSyntax SyntaxNodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (inputs k w xs)) : Derives Γ (existsConstructor k tag w xs) := by
  have ht := SyntaxNumerals.exists_numeral hZ tag w hw
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (numeral tag (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ T
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hi1 : Derives Ξ (inputs k w.castSucc (fun i => (xs i).castSucc)) := by simpa only [Formula.raise, inputs_rename] using under hi T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hn := SyntaxNodes.exists_node hZ1 k _ _ _ hw1 (.conjL hT) hi1
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (node k w.castSucc.castSucc (Fin.last m).castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1)))
  let Δ := Context.add N (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have ht2 : Derives Δ (numeral tag (Fin.last m).castSucc) := by simpa only [T, Formula.raise, numeral_rename] using under (Derives.conjR hT) N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hc := intro_constructor k tag w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) _ _ ht2 (.conjR hN)
  have hout : Derives Δ (existsConstructor k tag w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc)) := by
    apply Derives.exI (Fin.last (m+1))
    simp only [Formula.instantiate, Formula.rename, constructor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hN) hc
  simpa only [Formula.raise, existsConstructor_rename] using hout

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (constructor k tag w xs n)) (hr : Derives Γ (constructor k tag w xs r)) : Derives Γ (.equal n r) := by
  let N := constructorBody k tag w xs n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_constructor k tag w xs n _ hn
  have hr1 : Derives Ξ (constructor k tag w.castSucc (fun i => (xs i).castSucc) r.castSucc) := by simpa only [Formula.raise, constructor_rename] using under hr N
  let R := constructorBody k tag w.castSucc (fun i => (xs i).castSucc) r.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_constructor k tag w.castSucc (fun i => (xs i).castSucc) r.castSucc _ hr1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ N) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw N) R
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hN2 : Derives Δ ((numeral tag (Fin.last m).castSucc).conj
      (node k w.castSucc.castSucc (Fin.last m).castSucc (fun i => (xs i).castSucc.castSucc) n.castSucc.castSucc)) := by
    simpa only [N, constructorBody, Formula.raise, Formula.rename, numeral_rename, node_rename] using under hN R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have heq := SyntaxNumerals.unique hZ2 tag _ _ (.conjL hN2) (.conjL hR)
  have hnode := tag_subst k _ _ _ _ _ (eq_symm heq) (.conjR hR)
  exact SyntaxNodes.unique hZ2 k _ _ _ _ _ hw2 (.conjR hN2) hnode

theorem disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k l a b : Nat) (hab : a ≠ b)
    (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (constructor k a w xs n)) (hb : Derives Γ (constructor l b w ys n)) : Derives Γ .bot := by
  let A := constructorBody k a w xs n
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  apply eliminate_constructor k a w xs n _ ha
  have hb1 : Derives Ξ (constructor l b w.castSucc (fun i => (ys i).castSucc) n.castSucc) := by simpa only [Formula.raise, constructor_rename] using under hb A
  let B := constructorBody l b w.castSucc (fun i => (ys i).castSucc) n.castSucc
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  apply eliminate_constructor l b w.castSucc (fun i => (ys i).castSucc) n.castSucc _ hb1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ A) B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw A) B
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hA2 : Derives Δ ((numeral a (Fin.last m).castSucc).conj
      (node k w.castSucc.castSucc (Fin.last m).castSucc (fun i => (xs i).castSucc.castSucc) n.castSucc.castSucc)) := by
    simpa only [A, constructorBody, Formula.raise, Formula.rename, numeral_rename, node_rename] using under hA B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have heq := SyntaxNodes.tags_equal hZ2 k l _ _ _ _ _ _ hw2 (.conjR hA2) (.conjR hB)
  exact .impE (SyntaxNumerals.different hZ2 a b hab _ _ (.conjL hA2) (.conjL hB)) heq

theorem child_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (constructor k tag w xs n)) : Derives Γ (.mem (xs i) n) := by
  let N := constructorBody k tag w xs n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_constructor k tag w xs n _ hn
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  exact SyntaxNodes.child_member (ZFContext.under hZ N) k _ _ _ _ i hw1 (.conjR hN)

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (inputs k w xs)) : Derives Γ (constructorFiber k tag w xs) := by
  have he := exists_constructor hZ k tag w xs hw hi
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (constructor k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m))
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  change Derives Γ (.ex E) at he
  apply Derives.exE (p := E) he
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ E
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((constructor k tag w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let R := constructor k tag w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))
    let Δ := Context.add R (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 R
    have hn2 : Derives Δ (constructor k tag w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last m).castSucc) := by
      simpa only [E, Formula.raise, constructor_rename] using under (Derives.conjR hE) R
    exact unique (ZFContext.under hZ1 R) k tag _ _ _ _ hw2 (.hyp (Or.inl rfl)) hn2
  have hout : Derives Ξ (constructorFiber k tag w.castSucc (fun i => (xs i).castSucc)) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, constructor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hE hu
  simpa only [Formula.raise, constructorFiber_rename] using hout
end PPAC.Migration.Internal.SyntaxConstructors
