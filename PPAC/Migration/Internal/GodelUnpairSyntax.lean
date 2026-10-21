import PPAC.Migration.Internal.ObjectGodelPair

/-! 全内部自然码的解码关系及实际唯一纤维；所有分量均为对象变量。 -/
namespace PPAC.Migration.Internal.GodelUnpairSyntax
open Source SourceAlgebra SourceLogic GodelPairSyntax
open NaturalAdditionBounds (below below_rename)

def witness {m} (w p a b : Fin m) : Formula m :=
  ((Formula.mem a w).conj (.mem b w)).conj (code w a b p)
def preimage {m} (w p : Fin m) : Formula m := .ex (.ex
  (witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))
def exactAt {m} (w p a b : Fin m) : Formula m := .all (.all
  ((witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.equal (Fin.last m).castSucc a.castSucc.castSucc).conj (.equal (Fin.last (m+1)) b.castSucc.castSucc))))
def fiber {m} (w p : Fin m) : Formula m := .ex (.ex
  ((witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (exactAt w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))
def boundedFiber {m} (w p : Fin m) : Formula m := .ex (.ex
  (((witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (exactAt w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))).conj
      ((below (Fin.last m).castSucc p.castSucc.castSucc).conj (below (Fin.last (m+1)) p.castSucc.castSucc))))
def matrix : Formula 2 := preimage 0 1

theorem witness_rename {m k} (w p a b : Fin m) (r : Fin m → Fin k) :
    (witness w p a b).rename r = witness (r w) (r p) (r a) (r b) := by
  simp only [witness, Formula.rename, code_rename]
theorem preimage_rename {m k} (w p : Fin m) (r : Fin m → Fin k) :
    (preimage w p).rename r = preimage (r w) (r p) := by
  simp only [preimage, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem exactAt_rename {m k} (w p a b : Fin m) (r : Fin m → Fin k) :
    (exactAt w p a b).rename r = exactAt (r w) (r p) (r a) (r b) := by
  simp only [exactAt, Formula.iff, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem fiber_rename {m k} (w p : Fin m) (r : Fin m → Fin k) :
    (fiber w p).rename r = fiber (r w) (r p) := by
  simp only [fiber, Formula.rename, witness_rename, exactAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem boundedFiber_rename {m k} (w p : Fin m) (r : Fin m → Fin k) :
    (boundedFiber w p).rename r = boundedFiber (r w) (r p) := by
  simp only [boundedFiber, Formula.rename, witness_rename, exactAt_rename, below_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = preimage (ρ 0) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 2) = x := by
    change Fin.lastCases x ρ (Fin.last 1) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, preimage_rename, h0, h1]

theorem intro_preimage {m} {Γ : Context m} (w p a b : Fin m) (ha : Derives Γ (.mem a w))
    (hb : Derives Γ (.mem b w)) (hp : Derives Γ (code w a b p)) : Derives Γ (preimage w p) := by
  apply Derives.exI a
  apply Derives.exI b
  simp only [Formula.instantiate, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI ha hb) hp

theorem eliminate_preimage {m} {Γ : Context m} (w p : Fin m) (r : Formula m) (hp : Derives Γ (preimage w p))
    (hc : Derives (Context.add (witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
      (Context.image Formula.raise (Context.image Formula.raise Γ))) r.raise.raise) : Derives Γ r := by
  change Derives Γ (.ex (.ex _)) at hp
  apply Derives.exE hp
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, hs, he⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.Internal.GodelUnpairSyntax
