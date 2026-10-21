import PPAC.Migration.Internal.ObjectStructuralNode

/-! 原Nil/Cons的嵌套配数纯公式；零和标签一均为实际对象见证。 -/
namespace PPAC.Migration.Internal.StructuralListSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralNodeSyntax

def nilWitness {m} (w n : Fin m) : Formula (m+1) :=
  (empty (Fin.last m)).conj (raw w.castSucc (Fin.last m) (Fin.last m) n.castSucc)
def nilCode {m} (w n : Fin m) : Formula m := .ex (nilWitness w n)
def consAtWitness {m} (w e h t n : Fin m) : Formula (m+1) :=
  (GodelPairSyntax.code w.castSucc h.castSucc t.castSucc (Fin.last m)).conj
    (raw w.castSucc e.castSucc (Fin.last m) n.castSucc)
def consAt {m} (w e h t n : Fin m) : Formula m := .ex (consAtWitness w e h t n)
def consUnits {m} (w h t n : Fin m) : Formula (m+2) :=
  (empty (Fin.last m).castSucc).conj ((successor (Fin.last (m+1)) (Fin.last m).castSucc).conj
    (consAt w.castSucc.castSucc (Fin.last (m+1)) h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc))
def consCode {m} (w h t n : Fin m) : Formula m := .ex (.ex (consUnits w h t n))
def existsNil {m} (w : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (nilCode w.castSucc (Fin.last m)))
def fiberNil {m} (w : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (nilCode w.castSucc (Fin.last m))).conj (.all
    ((nilCode w.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))
def existsCons {m} (w h t : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (consCode w.castSucc h.castSucc t.castSucc (Fin.last m)))
def fiberCons {m} (w h t : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (consCode w.castSucc h.castSucc t.castSucc (Fin.last m))).conj (.all
    ((consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))
def unitWitness (m : Nat) : Formula (m+2) :=
  (empty (Fin.last m).castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)
def units (m : Nat) : Formula m := .ex (.ex (unitWitness m))

theorem nilCode_rename {m k} (w n : Fin m) (r : Fin m → Fin k) : (nilCode w n).rename r = nilCode (r w) (r n) := by
  simp only [nilCode, nilWitness, Formula.rename, empty_rename, raw_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem consAt_rename {m k} (w e h t n : Fin m) (r : Fin m → Fin k) :
    (consAt w e h t n).rename r = consAt (r w) (r e) (r h) (r t) (r n) := by
  simp only [consAt, consAtWitness, Formula.rename, GodelPairSyntax.code_rename, raw_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem consCode_rename {m k} (w h t n : Fin m) (r : Fin m → Fin k) :
    (consCode w h t n).rename r = consCode (r w) (r h) (r t) (r n) := by
  simp only [consCode, consUnits, Formula.rename, empty_rename, successor_rename, consAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem existsNil_rename {m k} (w : Fin m) (r : Fin m → Fin k) : (existsNil w).rename r = existsNil (r w) := by
  simp only [existsNil, Formula.rename, nilCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem fiberNil_rename {m k} (w : Fin m) (r : Fin m → Fin k) : (fiberNil w).rename r = fiberNil (r w) := by
  simp only [fiberNil, Formula.rename, nilCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem existsCons_rename {m k} (w h t : Fin m) (r : Fin m → Fin k) :
    (existsCons w h t).rename r = existsCons (r w) (r h) (r t) := by
  simp only [existsCons, Formula.rename, consCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem fiberCons_rename {m k} (w h t : Fin m) (r : Fin m → Fin k) :
    (fiberCons w h t).rename r = fiberCons (r w) (r h) (r t) := by
  simp only [fiberCons, Formula.rename, consCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_nil {m} {Γ : Context m} (w n z : Fin m) (hz : Derives Γ (empty z))
    (hn : Derives Γ (raw w z z n)) : Derives Γ (nilCode w n) := by
  apply Derives.exI z
  simp only [Formula.instantiate, nilWitness, Formula.rename, empty_rename, raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hz hn

theorem intro_consAt {m} {Γ : Context m} (w e h t n q : Fin m) (hq : Derives Γ (GodelPairSyntax.code w h t q))
    (hn : Derives Γ (raw w e q n)) : Derives Γ (consAt w e h t n) := by
  apply Derives.exI q
  simp only [Formula.instantiate, consAtWitness, Formula.rename, GodelPairSyntax.code_rename, raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hq hn

theorem intro_cons {m} {Γ : Context m} (w z e h t n : Fin m) (hz : Derives Γ (empty z))
    (he : Derives Γ (successor e z)) (hn : Derives Γ (consAt w e h t n)) : Derives Γ (consCode w h t n) := by
  apply Derives.exI z
  apply Derives.exI e
  simp only [Formula.instantiate, consUnits, Formula.rename, empty_rename, successor_rename, consAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hz (.conjI he hn)

theorem eliminate_nil {m} {Γ : Context m} (w n : Fin m) (r : Formula m) (hn : Derives Γ (nilCode w n))
    (hc : Derives (Context.add (nilWitness w n) (Context.image Formula.raise Γ)) r.raise) : Derives Γ r := .exE hn hc

theorem eliminate_consAt {m} {Γ : Context m} (w e h t n : Fin m) (r : Formula m) (hn : Derives Γ (consAt w e h t n))
    (hc : Derives (Context.add (consAtWitness w e h t n) (Context.image Formula.raise Γ)) r.raise) : Derives Γ r := .exE hn hc

theorem eliminate_cons {m} {Γ : Context m} (w h t n : Fin m) (r : Formula m) (hn : Derives Γ (consCode w h t n))
    (hc : Derives (Context.add (consUnits w h t n) (Context.image Formula.raise (Context.image Formula.raise Γ))) r.raise.raise) : Derives Γ r := by
  change Derives Γ (.ex (.ex _)) at hn
  apply Derives.exE hn
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, hs, he⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr hs, he⟩

theorem consAt_tag_subst {m} {Γ : Context m} (w e f h t n : Fin m) (he : Derives Γ (.equal e f))
    (hn : Derives Γ (consAt w e h t n)) : Derives Γ (consAt w f h t n) := by
  have hi : Derives Γ ((consAt w.castSucc (Fin.last m) h.castSucc t.castSucc n.castSucc).instantiate e) := by
    simpa only [Formula.instantiate, consAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hn
  have ho := Derives.eqSubst (consAt w.castSucc (Fin.last m) h.castSucc t.castSucc n.castSucc) he hi
  simpa only [Formula.instantiate, consAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.StructuralListSyntax
