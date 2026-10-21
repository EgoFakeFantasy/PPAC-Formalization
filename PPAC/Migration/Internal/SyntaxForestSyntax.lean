import PPAC.Migration.Internal.SyntaxNumerals

/-! 固定有限字段数的原Nil/Cons向量；k索引有限公式，字段值及候选码均为内部对象。 -/
namespace PPAC.Migration.Internal.SyntaxForestSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax

def inputs {m} : (k : Nat) → Fin m → (Fin k → Fin m) → Formula m
  | 0, w, _ => .equal w w
  | k+1, w, xs => (Formula.mem (xs 0) w).conj (inputs k w (fun i => xs i.succ))

def forest {m} : (k : Nat) → Fin m → (Fin k → Fin m) → Fin m → Formula m
  | 0, w, _, n => nilCode w n
  | k+1, w, xs, n => .ex ((Formula.mem (xs 0).castSucc w.castSucc).conj
      ((forest k w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m)).conj
        (consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc)))

def existsForest {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (forest k w.castSucc (fun i => (xs i).castSucc) (Fin.last m)))

theorem inputs_rename {m n} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (s : Fin m → Fin n) :
    (inputs k w xs).rename s = inputs k (s w) (fun i => s (xs i)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [inputs, Formula.rename, ih]

theorem forest_rename {m n} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (x : Fin m) (s : Fin m → Fin n) :
    (forest k w xs x).rename s = forest k (s w) (fun i => s (xs i)) (s x) := by
  induction k generalizing m n with
  | zero => exact nilCode_rename w x s
  | succ k ih =>
    simp only [forest, Formula.rename, ih, consCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsForest_rename {m n} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (s : Fin m → Fin n) :
    (existsForest k w xs).rename s = existsForest k (s w) (fun i => s (xs i)) := by
  simp only [existsForest, Formula.rename, forest_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem inputs_at {m} {Γ : Context m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (i : Fin k)
    (hs : Derives Γ (inputs k w xs)) : Derives Γ (.mem (xs i) w) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .conjL hs
    · exact ih (fun a => xs a.succ) j (.conjR hs)

theorem intro_inputs {m} {Γ : Context m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (hs : ∀ i, Derives Γ (.mem (xs i) w)) : Derives Γ (inputs k w xs) := by
  induction k with
  | zero => exact .eqRefl w
  | succ k ih => exact .conjI (hs 0) (ih (fun i => xs i.succ) (fun i => hs i.succ))

theorem intro_cons {m} {Γ : Context m} (k : Nat) (w : Fin m) (xs : Fin (k+1) → Fin m) (n t : Fin m)
    (hh : Derives Γ (.mem (xs 0) w)) (ht : Derives Γ (forest k w (fun i => xs i.succ) t))
    (hc : Derives Γ (consCode w (xs 0) t n)) : Derives Γ (forest (k+1) w xs n) := by
  apply Derives.exI t
  simp only [Formula.instantiate, Formula.rename, forest_rename, consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hh (.conjI ht hc)

theorem eliminate_cons {m} {Γ : Context m} (k : Nat) (w : Fin m) (xs : Fin (k+1) → Fin m) (n : Fin m) (q : Formula m)
    (hn : Derives Γ (forest (k+1) w xs n))
    (hc : Derives (Context.add ((Formula.mem (xs 0).castSucc w.castSucc).conj
      ((forest k w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m)).conj
        (consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))) (Context.image Formula.raise Γ)) q.raise) : Derives Γ q := .exE hn hc

theorem cons_tail_subst {m} {Γ : Context m} (w h t u n : Fin m) (he : Derives Γ (.equal t u))
    (hc : Derives Γ (consCode w h t n)) : Derives Γ (consCode w h u n) := by
  have hi : Derives Γ ((consCode w.castSucc h.castSucc (Fin.last m) n.castSucc).instantiate t) := by
    simpa only [Formula.instantiate, consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (consCode w.castSucc h.castSucc (Fin.last m) n.castSucc) he hi
  simpa only [Formula.instantiate, consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
theorem intro_exists {m} {Γ : Context m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (hn : Derives Γ (.mem n w)) (hf : Derives Γ (forest k w xs n)) : Derives Γ (existsForest k w xs) := by
  apply Derives.exI n
  simp only [Formula.instantiate, Formula.rename, forest_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hn hf
end PPAC.Migration.Internal.SyntaxForestSyntax
