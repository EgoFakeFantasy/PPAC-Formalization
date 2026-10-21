import PPAC.Migration.Internal.StructuralNodeSyntax

/-! 原配数与内部归纳集合的实际后继见证构造全部原始节点。 -/
namespace PPAC.Migration.Internal.StructuralNodeExistence
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralNodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_raw {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag payload : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hp : Derives Γ (.mem payload w)) : Derives Γ (existsRaw w tag payload) := by
  have hq := GodelPairCore.exists_code hZ w tag payload hw ht hp
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (GodelPairSyntax.code w.castSucc tag.castSucc payload.castSucc (Fin.last m))
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at hq
  apply Derives.exE (p := Q) hq
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hn := Derives.impE (step_at w.castSucc (Fin.last m) (.conjL hw1)) (.conjL hQ)
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)
  let Δ := Context.add N (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hQ2 : Derives Δ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (GodelPairSyntax.code w.castSucc.castSucc tag.castSucc.castSucc payload.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [Q, Formula.raise, Formula.rename, GodelPairSyntax.code_rename] using under hQ N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hr := intro_raw _ _ _ _ _ (.conjR hQ2) (.conjR hN)
  have hout := intro_existsRaw _ _ _ _ (.conjL hN) hr
  simpa only [Formula.raise, existsRaw_rename] using hout
end PPAC.Migration.Internal.StructuralNodeExistence
