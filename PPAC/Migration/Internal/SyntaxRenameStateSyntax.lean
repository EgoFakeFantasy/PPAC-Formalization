import PPAC.Migration.Internal.SyntaxMapLiftFiber

/-! 完整公式重命名的七个内部自然状态字段；源码是递归索引，不混入状态。 -/
namespace PPAC.Migration.Internal.SyntaxRenameStateSyntax
open Source SourceAlgebra SourceLogic SyntaxForestSyntax SyntaxMapCodeSyntax FormulaCodeSyntax

def seven {m} (r s a b c d q : Fin m) : Fin 7 → Fin m := Fin.cases r (Fin.cases s (Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (Fin.cases q (Fin.elim0)))))))

def cell {m} (w r s a b c d q h : Fin m) : Formula m := forest 7 w (seven r s a b c d q) h

def legal {m} (w r s a b c d q : Fin m) : Formula m := (mapCode w a c r).conj ((mapCode w b d s).conj (formulaCode w q c d))

def state {m} (w r s a b c d q h : Fin m) : Formula m := (cell w r s a b c d q h).conj (legal w r s a b c d q)

def equalParams {m} (r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) : Formula m :=
  (Formula.equal r r1).conj ((Formula.equal s s1).conj ((Formula.equal a a1).conj ((Formula.equal b b1).conj ((Formula.equal c c1).conj ((Formula.equal d d1).conj (Formula.equal q q1))))))

def uniqueParams {m} (w h r s a b c d q : Fin m) : Formula m := .all (.all (.all (.all (.all (.all (.all ((cell w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).imp
    (equalParams (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) r.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))))))))

def stateBody {m} (w h : Fin m) : Formula (m+7) := state w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc

def recognized {m} (w h : Fin m) : Formula m := .ex (.ex (.ex (.ex (.ex (.ex (.ex (stateBody w h)))))))

def decodedFiber {m} (w h : Fin m) : Formula m := .ex (.ex (.ex (.ex (.ex (.ex (.ex ((stateBody w h).conj (uniqueParams w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6))))))))))

def existsState {m} (w r s a b c d q : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (state w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m)))

def stateFiber {m} (w r s a b c d q : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (state w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m))).conj
    (.all ((cell w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem seven_map {m n} (r s a b c d q : Fin m) (ρ : Fin m → Fin n) :
    (fun j => ρ (seven r s a b c d q j)) = seven (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  funext j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  exact Fin.cases rfl (fun j => Fin.elim0 j) j

theorem cell_rename {m n} (w r s a b c d q h : Fin m) (ρ : Fin m → Fin n) :
    (cell w r s a b c d q h).rename ρ = cell (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) (ρ h) := by
  simp only [cell, forest_rename, seven_map]

theorem legal_rename {m n} (w r s a b c d q : Fin m) (ρ : Fin m → Fin n) :
    (legal w r s a b c d q).rename ρ = legal (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [legal, Formula.rename, mapCode_rename, formulaCode_rename]

theorem state_rename {m n} (w r s a b c d q h : Fin m) (ρ : Fin m → Fin n) :
    (state w r s a b c d q h).rename ρ = state (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) (ρ h) := by
  simp only [state, Formula.rename, cell_rename, legal_rename]

theorem equalParams_rename {m n} (r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) (ρ : Fin m → Fin n) :
    (equalParams r s a b c d q r1 s1 a1 b1 c1 d1 q1).rename ρ = equalParams (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) (ρ r1) (ρ s1) (ρ a1) (ρ b1) (ρ c1) (ρ d1) (ρ q1) := rfl

theorem uniqueParams_rename {m n} (w h r s a b c d q : Fin m) (ρ : Fin m → Fin n) :
    (uniqueParams w h r s a b c d q).rename ρ = uniqueParams (ρ w) (ρ h) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [uniqueParams, Formula.rename, cell_rename, equalParams_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem recognized_rename {m n} (w h : Fin m) (ρ : Fin m → Fin n) :
    (recognized w h).rename ρ = recognized (ρ w) (ρ h) := by
  simp only [recognized, stateBody, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem decodedFiber_rename {m n} (w h : Fin m) (ρ : Fin m → Fin n) :
    (decodedFiber w h).rename ρ = decodedFiber (ρ w) (ρ h) := by
  simp only [decodedFiber, stateBody, Formula.rename, state_rename, uniqueParams_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsState_rename {m n} (w r s a b c d q : Fin m) (ρ : Fin m → Fin n) :
    (existsState w r s a b c d q).rename ρ = existsState (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [existsState, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem stateFiber_rename {m n} (w r s a b c d q : Fin m) (ρ : Fin m → Fin n) :
    (stateFiber w r s a b c d q).rename ρ = stateFiber (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [stateFiber, Formula.rename, state_rename, cell_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem under_seven {m} {Γ : Context m} {P : Formula m} (hp : Derives Γ P) (B : Formula (m+7)) :
    Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))))) P.raise.raise.raise.raise.raise.raise.raise :=
  .weaken (fun _ h => Or.inr h) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hp))))))))

theorem zf_under_seven {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (B : Formula (m+7)) :
    ZFContext.Evidence (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))))) := ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) B

theorem eliminate_seven {m} {Γ : Context m} (B : Formula (m+7)) (Q : Formula m)
    (he : Derives Γ (.ex (.ex (.ex (.ex (.ex (.ex (.ex (B)))))))))
    (hc : Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))))) Q.raise.raise.raise.raise.raise.raise.raise) : Derives Γ Q := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨s1, ⟨s2, ⟨s3, ⟨s4, ⟨s5, ⟨s6, hs, h6⟩, h5⟩, h4⟩, h3⟩, h2⟩, h1⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨s1, Or.inr ⟨s2, Or.inr ⟨s3, Or.inr ⟨s4, Or.inr ⟨s5, Or.inr ⟨s6, Or.inr hs, h6⟩, h5⟩, h4⟩, h3⟩, h2⟩, h1⟩

theorem intro_recognized {m} {Γ : Context m} (w h r s a b c d q : Fin m)
    (hs : Derives Γ (state w r s a b c d q h)) : Derives Γ (recognized w h) := by
  apply Derives.exI r
  apply Derives.exI s
  apply Derives.exI a
  apply Derives.exI b
  apply Derives.exI c
  apply Derives.exI d
  apply Derives.exI q
  simp only [stateBody, Formula.instantiate, state_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact hs

theorem intro_decoded {m} {Γ : Context m} (w h r s a b c d q : Fin m)
    (hs : Derives Γ (state w r s a b c d q h)) (hu : Derives Γ (uniqueParams w h r s a b c d q)) : Derives Γ (decodedFiber w h) := by
  apply Derives.exI r
  apply Derives.exI s
  apply Derives.exI a
  apply Derives.exI b
  apply Derives.exI c
  apply Derives.exI d
  apply Derives.exI q
  simp only [stateBody, Formula.instantiate, Formula.rename, state_rename, uniqueParams_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs hu

end PPAC.Migration.Internal.SyntaxRenameStateSyntax
