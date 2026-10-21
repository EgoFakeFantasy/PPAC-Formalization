import PPAC.Migration.Internal.SyntaxNodeSyntax

/-! 精确有限字段原节点的实际存在唯一、内部scalar单射及严格子字段界。 -/
namespace PPAC.Migration.Internal.SyntaxNodes
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForestSyntax SyntaxNodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_node {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hi : Derives Γ (inputs k w xs)) : Derives Γ (existsNode k w tag xs) := by
  have hp := SyntaxForests.exists_forest hZ k w xs hw hi
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (forest k w.castSucc (fun i => (xs i).castSucc) (Fin.last m))
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ P
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hn := StructuralNodeExistence.exists_raw hZ1 _ _ _ hw1 (under ht P) (.conjL hP)
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (StructuralNodeSyntax.raw w.castSucc.castSucc tag.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add N (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hP2 : Derives Δ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (forest k w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last m).castSucc)) := by
    simpa only [P, Formula.raise, Formula.rename, forest_rename] using under hP N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hc := intro_node k w.castSucc.castSucc tag.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) _ _ (under (under ht P) N) (.conjR hP2) (.conjR hN)
  have hout : Derives Δ (existsNode k w.castSucc.castSucc tag.castSucc.castSucc (fun i => (xs i).castSucc.castSucc)) := by
    apply Derives.exI (Fin.last (m+1))
    simp only [Formula.instantiate, Formula.rename, node_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hN) hc
  simpa only [Formula.raise, existsNode_rename] using hout

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (node k w tag xs n)) : Derives Γ (.mem n w) := by
  let N := nodeBody k w tag xs n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_node k w tag xs n _ hn
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  exact StructuralNodeProperties.range (ZFContext.under hZ N) _ _ _ _ hw1 (.conjR (.conjR hN))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (node k w tag xs n)) (hr : Derives Γ (node k w tag xs r)) : Derives Γ (.equal n r) := by
  let N := nodeBody k w tag xs n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_node k w tag xs n _ hn
  have hr1 : Derives Ξ (node k w.castSucc tag.castSucc (fun i => (xs i).castSucc) r.castSucc) := by simpa only [Formula.raise, node_rename] using under hr N
  let R := nodeBody k w.castSucc tag.castSucc (fun i => (xs i).castSucc) r.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_node k w.castSucc tag.castSucc (fun i => (xs i).castSucc) r.castSucc _ hr1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ N) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw N) R
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hN2 : Derives Δ ((Formula.mem tag.castSucc.castSucc w.castSucc.castSucc).conj
      ((forest k w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last m).castSucc).conj
        (StructuralNodeSyntax.raw w.castSucc.castSucc tag.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc))) := by
    simpa only [N, nodeBody, Formula.raise, Formula.rename, forest_rename, StructuralNodeSyntax.raw_rename] using under hN R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have heq := SyntaxForests.unique hZ2 k _ _ _ _ hw2 (.conjL (.conjR hN2)) (.conjL (.conjR hR))
  have hraw := StructuralTreeEncode.raw_payload_subst _ _ _ _ _ (eq_symm heq) (.conjR (.conjR hR))
  exact StructuralNodeCore.unique hZ2 _ _ _ _ _ hw2 (.conjL hN2) (SyntaxForests.range hZ2 k _ _ _ hw2 (.conjL (.conjR hN2))) (.conjR (.conjR hN2)) hraw

theorem tags_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k l : Nat) (w a b : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (node k w a xs n)) (hb : Derives Γ (node l w b ys n)) : Derives Γ (.equal a b) := by
  let A := nodeBody k w a xs n
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  apply eliminate_node k w a xs n _ ha
  have hb1 : Derives Ξ (node l w.castSucc b.castSucc (fun i => (ys i).castSucc) n.castSucc) := by simpa only [Formula.raise, node_rename] using under hb A
  let B := nodeBody l w.castSucc b.castSucc (fun i => (ys i).castSucc) n.castSucc
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  apply eliminate_node l w.castSucc b.castSucc (fun i => (ys i).castSucc) n.castSucc _ hb1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ A) B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw A) B
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hA2 : Derives Δ ((Formula.mem a.castSucc.castSucc w.castSucc.castSucc).conj
      ((forest k w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last m).castSucc).conj
        (StructuralNodeSyntax.raw w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc))) := by
    simpa only [A, nodeBody, Formula.raise, Formula.rename, forest_rename, StructuralNodeSyntax.raw_rename] using under hA B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hp := SyntaxForests.range hZ2 k _ _ _ hw2 (.conjL (.conjR hA2))
  have hq := SyntaxForests.range hZ2 l _ _ _ hw2 (.conjL (.conjR hB))
  exact .conjL (StructuralNodeCore.injective hZ2 _ _ _ _ _ _ hw2 (.conjL hA2) hp (.conjL hB) hq (.conjR (.conjR hA2)) (.conjR (.conjR hB)))

theorem child_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (node k w tag xs n)) : Derives Γ (.mem (xs i) n) := by
  let N := nodeBody k w tag xs n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_node k w tag xs n _ hn
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hp := SyntaxForests.range hZ1 k _ _ _ hw1 (.conjL (.conjR hN))
  have hchild := SyntaxForests.entry_member hZ1 k _ _ _ i hw1 (.conjL (.conjR hN))
  have hraw := Derives.conjR (Derives.conjR hN)
  have hb := StructuralNodeProperties.components hZ1 _ _ _ _ hw1 (.conjL hN) hp hraw
  have hnW := StructuralNodeProperties.range hZ1 _ _ _ _ hw1 hraw
  have ho := NaturalOrderBasic.ordinal hZ1 _ _ hw1 hnW
  have hsub := OrdinalTransitivity.subset_of_member _ _ (.conjL ho) (.conjR hb)
  exact .impE (RestrictionSyntax.subset_at _ _ _ hsub) hchild
theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hi : Derives Γ (inputs k w xs)) : Derives Γ (nodeFiber k w tag xs) := by
  have he := exists_node hZ k w tag xs hw ht hi
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (node k w.castSucc tag.castSucc (fun i => (xs i).castSucc) (Fin.last m))
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  change Derives Γ (.ex E) at he
  apply Derives.exE (p := E) he
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ E
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((node k w.castSucc.castSucc tag.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let R := node k w.castSucc.castSucc tag.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))
    let Δ := Context.add R (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 R
    have hn2 : Derives Δ (node k w.castSucc.castSucc tag.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last m).castSucc) := by
      simpa only [E, Formula.raise, node_rename] using under (Derives.conjR hE) R
    exact unique (ZFContext.under hZ1 R) k _ _ _ _ _ hw2 (.hyp (Or.inl rfl)) hn2
  have hout : Derives Ξ (nodeFiber k w.castSucc tag.castSucc (fun i => (xs i).castSucc)) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, node_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hE hu
  simpa only [Formula.raise, nodeFiber_rename] using hout
end PPAC.Migration.Internal.SyntaxNodes
