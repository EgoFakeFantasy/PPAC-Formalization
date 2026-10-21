import PPAC.Migration.Internal.StructuralTreeCheck

/-! 消去实际零/单位标志的原树有效性、无效性及精确实际节点解码公式。 -/
namespace PPAC.Migration.Internal.StructuralTreeValiditySyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax
open StructuralTreeOperatorSyntax (shape shape_rename)
open StructuralTreeRecursiveSyntax (accepts accepts_rename rejects rejects_rename)

def validWitness {m} (w n : Fin m) : Formula (m+2) :=
  ((empty (Fin.last m).castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)).conj
    (accepts w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc)

def invalidWitness {m} (w n : Fin m) : Formula (m+2) :=
  ((empty (Fin.last m).castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)).conj
    (rejects w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc)

def valid {m} (w n : Fin m) : Formula m := (Formula.mem n w).conj (.ex (.ex (validWitness w n)))

def invalid {m} (w n : Fin m) : Formula m := (Formula.mem n w).conj (.ex (.ex (invalidWitness w n)))

def validChildren {m} (w f : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp (valid w.castSucc.castSucc (Fin.last (m+1)))))

def nodeData {m} (w n tag p l f : Fin m) : Formula m := (shape w n tag p l f).conj (validChildren w f)

def dataBody {m} (w n : Fin m) : Formula (m+4) := nodeData w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
  (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))

def recursive {m} (w n : Fin m) : Formula m := .ex (.ex (.ex (.ex (dataBody w n))))

def uniqueData {m} (w n tag p l f : Fin m) : Formula m := .all (.all (.all (.all
  ((nodeData w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))).imp
      (((Formula.equal (Fin.last m).castSucc.castSucc.castSucc tag.castSucc.castSucc.castSucc.castSucc).conj
        (.equal (Fin.last (m+1)).castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc)).conj
        ((Formula.equal (Fin.last (m+2)).castSucc l.castSucc.castSucc.castSucc.castSucc).conj
          (.equal (Fin.last (m+3)) f.castSucc.castSucc.castSucc.castSucc)))))))

def decodedFiber {m} (w n : Fin m) : Formula m := .ex (.ex (.ex (.ex
  ((dataBody w n).conj (uniqueData w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)))))))

theorem valid_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (valid w n).rename s = valid (s w) (s n) := by
  simp only [valid, validWitness, Formula.rename, empty_rename, successor_rename, accepts_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem invalid_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (invalid w n).rename s = invalid (s w) (s n) := by
  simp only [invalid, invalidWitness, Formula.rename, empty_rename, successor_rename, rejects_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem validChildren_rename {m k} (w f : Fin m) (s : Fin m → Fin k) : (validChildren w f).rename s = validChildren (s w) (s f) := by
  simp only [validChildren, Formula.rename, edge_rename, valid_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem nodeData_rename {m k} (w n tag p l f : Fin m) (s : Fin m → Fin k) : (nodeData w n tag p l f).rename s = nodeData (s w) (s n) (s tag) (s p) (s l) (s f) := by
  simp only [nodeData, Formula.rename, shape_rename, validChildren_rename]

theorem recursive_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (recursive w n).rename s = recursive (s w) (s n) := by
  simp only [recursive, dataBody, Formula.rename, nodeData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueData_rename {m k} (w n tag p l f : Fin m) (s : Fin m → Fin k) : (uniqueData w n tag p l f).rename s = uniqueData (s w) (s n) (s tag) (s p) (s l) (s f) := by
  simp only [uniqueData, Formula.rename, nodeData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem decodedFiber_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (decodedFiber w n).rename s = decodedFiber (s w) (s n) := by
  simp only [decodedFiber, dataBody, Formula.rename, nodeData_rename, uniqueData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_valid {m} {Γ : Context m} (w z e n : Fin m) (hn : Derives Γ (.mem n w))
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (ha : Derives Γ (accepts w z e n)) : Derives Γ (valid w n) := by
  apply Derives.conjI hn
  apply Derives.exI z
  apply Derives.exI e
  simp only [validWitness, Formula.instantiate, Formula.rename, empty_rename, successor_rename, accepts_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hz he) ha

theorem intro_invalid {m} {Γ : Context m} (w z e n : Fin m) (hn : Derives Γ (.mem n w))
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (ha : Derives Γ (rejects w z e n)) : Derives Γ (invalid w n) := by
  apply Derives.conjI hn
  apply Derives.exI z
  apply Derives.exI e
  simp only [invalidWitness, Formula.instantiate, Formula.rename, empty_rename, successor_rename, rejects_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hz he) ha

theorem eliminate_valid {m} {Γ : Context m} (w n : Fin m) (q : Formula m) (hv : Derives Γ (valid w n))
    (hc : Derives (Context.add (validWitness w n) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  have h := Derives.conjR hv
  apply Derives.exE h
  apply Derives.exE (p := validWitness w n) (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨t, ht, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨t, Or.inr ht, he⟩

theorem eliminate_invalid {m} {Γ : Context m} (w n : Fin m) (q : Formula m) (hv : Derives Γ (invalid w n))
    (hc : Derives (Context.add (invalidWitness w n) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  have h := Derives.conjR hv
  apply Derives.exE h
  apply Derives.exE (p := invalidWitness w n) (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨t, ht, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨t, Or.inr ht, he⟩

theorem validChildren_at {m} {Γ : Context m} (w f i y : Fin m) (hv : Derives Γ (validChildren w f))
    (he : Derives Γ (edge f i y)) : Derives Γ (valid w y) := by
  have h : Derives Γ ((edge f i y).imp (valid w y)) := by
    simpa only [validChildren, Formula.instantiate, Formula.rename, edge_rename, valid_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE i hv)
  exact .impE h he

theorem intro_recursive {m} {Γ : Context m} (w n tag p l f : Fin m) (hd : Derives Γ (nodeData w n tag p l f)) : Derives Γ (recursive w n) := by
  apply Derives.exI tag
  apply Derives.exI p
  apply Derives.exI l
  apply Derives.exI f
  simpa only [dataBody, Formula.instantiate, nodeData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

theorem eliminate_recursive {m} {Γ : Context m} (w n : Fin m) (q : Formula m) (hr : Derives Γ (recursive w n))
    (hc : Derives (Context.add (dataBody w n) (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))) q.raise.raise.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (.ex (.ex _)))) at hr
  apply Derives.exE hr
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, ⟨t, ⟨u, hu, h1⟩, h2⟩, h3⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ⟨u, Or.inr hu, h1⟩, h2⟩, h3⟩
end PPAC.Migration.Internal.StructuralTreeValiditySyntax
