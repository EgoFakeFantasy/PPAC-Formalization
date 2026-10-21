import PPAC.Migration.Internal.FormulaCodeConstructSyntax

/-! 原实际构造纤维与对象类型定律连接；唯一性保持到所有原构造候选。 -/
namespace PPAC.Migration.Internal.FormulaCodeConstruct
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxForestSyntax FormulaCodeSyntax FormulaCodeConstructSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (b f : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (inputs k w xs)) (hl : Derives Γ (law k tag w xs b f)) :
    Derives Γ (typedFiber k tag w xs b f) := by
  have he := SyntaxConstructors.exists_unique hZ k tag w xs hw hi
  let N := ((Formula.mem (Fin.last m) w.castSucc).conj
    (constructor k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m))).conj
      (.all ((constructor k tag w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply Derives.exE (p := N) he
  have hl1 : Derives Δ (law k tag w.castSucc (fun i => (xs i).castSucc) b.castSucc f.castSucc) := by
    simpa only [Formula.raise, law_rename] using under hl N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have ht := law_at k tag w.castSucc (fun i => (xs i).castSucc) b.castSucc f.castSucc (Fin.last m) hl1 (.conjR (.conjL hN))
  have hout : Derives Δ (typedFiber k tag w.castSucc (fun i => (xs i).castSucc) b.castSucc f.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, typedAt_rename, constructor_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjI (.conjL (.conjL hN)) (.conjI (.conjR (.conjL hN)) ht)) (.conjR hN)
  simpa only [Formula.raise, typedFiber_rename] using hout

theorem exists_of_fiber {m} {Γ : Context m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (b f : Fin m)
    (he : Derives Γ (typedFiber k tag w xs b f)) : Derives Γ (typedExists k tag w xs b f) := by
  let N := ((Formula.mem (Fin.last m) w.castSucc).conj
    (typedAt k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m) b.castSucc f.castSucc)).conj
      (.all ((constructor k tag w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply Derives.exE (p := N) he
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hout : Derives Δ (typedExists k tag w.castSucc (fun i => (xs i).castSucc) b.castSucc f.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, typedAt_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjL hN
  simpa only [Formula.raise, typedExists_rename] using hout
end PPAC.Migration.Internal.FormulaCodeConstruct
