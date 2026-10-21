import PPAC.Migration.Internal.SyntaxAtomTyping

/-! 合法内部上下文和纯项实际构造原常量/membership/equal码，保留给定原输入。 -/
namespace PPAC.Migration.Internal.SyntaxAtomExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxForestSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxAtomLogic
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nullary_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f : Fin m)
    (hw : Derives Γ (omega w)) (hctx : Derives Γ (contexts w b f)) : Derives Γ (existsNullary truth w b f) := by
  have hn := SyntaxConstructors.exists_constructor hZ 0 (nullaryTag truth) w Fin.elim0 hw (.eqRefl w)
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (constructor 0 (nullaryTag truth) w.castSucc Fin.elim0 (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hx : Derives Γ (.ex N) := by simpa only [existsConstructor, zero_map] using hn
  apply Derives.exE (p := N) hx
  have hctx1 : Derives Δ (contexts w.castSucc b.castSucc f.castSucc) := by simpa only [Formula.raise, contexts_rename] using under hctx N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hout : Derives Δ (existsNullary truth w.castSucc b.castSucc f.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, nullary_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hN) (.conjI hctx1 (.conjR hN))
  simpa only [Formula.raise, existsNullary_rename] using hout

theorem membership_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (term w b f x)) (hy : Derives Γ (term w b f y)) : Derives Γ (existsMembership w b f x y) := by
  have hs := SyntaxConstructors.exists_constructor hZ 0 0 w Fin.elim0 hw (.eqRefl w)
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (zeroScalar w.castSucc (Fin.last m))
  let Ξ := Context.add S (Context.image Formula.raise Γ)
  have hz : Derives Γ (.ex S) := by simpa only [S, existsConstructor, zeroScalar, zero_map] using hs
  apply Derives.exE (p := S) hz
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ S
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw S
  have hx1 : Derives Ξ (term w.castSucc b.castSucc f.castSucc x.castSucc) := by simpa only [Formula.raise, term_rename] using under hx S
  have hy1 : Derives Ξ (term w.castSucc b.castSucc f.castSucc y.castSucc) := by simpa only [Formula.raise, term_rename] using under hy S
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hi : Derives Ξ (inputs 3 w.castSucc (three (Fin.last m) x.castSucc y.castSucc)) :=
    .conjI (.conjL hS) (.conjI (SyntaxTerms.range hZ1 _ _ _ _ hw1 hx1) (.conjI (SyntaxTerms.range hZ1 _ _ _ _ hw1 hy1) (.eqRefl _)))
  have hn := SyntaxConstructors.exists_constructor hZ1 3 2 _ _ hw1 hi
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (memberCode w.castSucc.castSucc (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add N (Context.image Formula.raise Ξ)
  have hnat : Derives Ξ (.ex N) := by simpa only [N, existsConstructor, memberCode, three_map] using hn
  apply Derives.exE (p := N) hnat
  have hs2 : Derives Δ (zeroScalar w.castSucc.castSucc (Fin.last m).castSucc) := by simpa only [Formula.raise, zeroScalar_rename] using under (Derives.conjR hS) N
  have hx2 : Derives Δ (term w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc x.castSucc.castSucc) := by simpa only [Formula.raise, term_rename] using under hx1 N
  have hy2 : Derives Δ (term w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc y.castSucc.castSucc) := by simpa only [Formula.raise, term_rename] using under hy1 N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hd : Derives Δ (memberAt w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1))) :=
    .conjI (.conjI hs2 (.conjI hx2 hy2)) (.conjR hN)
  have hout : Derives Δ (existsMembership w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simp only [Formula.instantiate, Formula.rename, memberAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    apply Derives.conjI
    · exact .conjL hN
    · apply Derives.exI (Fin.last m).castSucc
      simpa only [Formula.instantiate, memberAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd
  simpa only [Formula.raise, existsMembership_rename] using hout

theorem equality_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (term w b f x)) (hy : Derives Γ (term w b f y)) : Derives Γ (existsEquality w b f x y) := by
  have hi : Derives Γ (inputs 2 w (two x y)) := .conjI (SyntaxTerms.range hZ _ _ _ _ hw hx) (.conjI (SyntaxTerms.range hZ _ _ _ _ hw hy) (.eqRefl _))
  have hn := SyntaxConstructors.exists_constructor hZ 2 3 _ _ hw hi
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (equalCode w.castSucc x.castSucc y.castSucc (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hnat : Derives Γ (.ex N) := by simpa only [N, existsConstructor, equalCode, two_map] using hn
  apply Derives.exE (p := N) hnat
  have hx1 : Derives Δ (term w.castSucc b.castSucc f.castSucc x.castSucc) := by simpa only [Formula.raise, term_rename] using under hx N
  have hy1 : Derives Δ (term w.castSucc b.castSucc f.castSucc y.castSucc) := by simpa only [Formula.raise, term_rename] using under hy N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hd : Derives Δ (equalAt w.castSucc b.castSucc f.castSucc x.castSucc y.castSucc (Fin.last m)) := .conjI (.conjI hx1 hy1) (.conjR hN)
  have hout : Derives Δ (existsEquality w.castSucc b.castSucc f.castSucc x.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, equalAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hN) hd
  simpa only [Formula.raise, existsEquality_rename] using hout
end PPAC.Migration.Internal.SyntaxAtomExistence
