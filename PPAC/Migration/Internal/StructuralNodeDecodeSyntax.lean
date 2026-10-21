import PPAC.Migration.Internal.StructuralNodeCore

/-! 原节点的自然标签/载荷解码关系；严格子码界保留为真实成员关系。 -/
namespace PPAC.Migration.Internal.StructuralNodeDecodeSyntax
open Source SourceAlgebra SourceLogic StructuralNodeSyntax

def witness {m} (w p a b : Fin m) : Formula m :=
  ((Formula.mem a w).conj (.mem b w)).conj (raw w a b p)
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
      ((Formula.mem (Fin.last m).castSucc p.castSucc.castSucc).conj (Formula.mem (Fin.last (m+1)) p.castSucc.castSucc))))

theorem witness_rename {m k} (w p a b : Fin m) (r : Fin m → Fin k) :
    (witness w p a b).rename r = witness (r w) (r p) (r a) (r b) := by
  simp only [witness, Formula.rename, raw_rename]
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
  simp only [boundedFiber, Formula.rename, witness_rename, exactAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_preimage {m} {Γ : Context m} (w p a b : Fin m) (ha : Derives Γ (.mem a w))
    (hb : Derives Γ (.mem b w)) (hp : Derives Γ (raw w a b p)) : Derives Γ (preimage w p) := by
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
end PPAC.Migration.Internal.StructuralNodeDecodeSyntax
