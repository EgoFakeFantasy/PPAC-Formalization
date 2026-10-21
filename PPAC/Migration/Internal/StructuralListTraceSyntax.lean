import PPAC.Migration.Internal.ObjectStructuralList
import PPAC.Migration.Internal.CheckedSequence

/-! 内部有限列表构造轨迹；长度、完整序列图、索引和值均是对象变量。 -/
namespace PPAC.Migration.Internal.StructuralListTraceSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax StructuralListSyntax

def step {m} (w a b : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (consCode w.castSucc (Fin.last m) a.castSucc b.castSucc))
def rowWitness {m} (w f i : Fin m) : Formula (m+3) :=
  (successor (Fin.last m).castSucc.castSucc i.castSucc.castSucc.castSucc).conj
    ((edge f.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc).conj
      ((edge f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))).conj
        (step w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))
def row {m} (w f i : Fin m) : Formula m := .ex (.ex (.ex (rowWitness w f i)))
def links {m} (w l f : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) l.castSucc).imp (row w.castSucc f.castSucc (Fin.last m)))
def frame {m} (w z e l d f : Fin m) : Formula m := ((empty z).conj (nilCode w e)).conj
  (((Formula.mem l w).conj (successor d l)).conj
    ((sequence f d w).conj ((edge f z e).conj (links w l f))))
def trace {m} (w z e l d f n : Fin m) : Formula m := (frame w z e l d f).conj (edge f l n)
def existsTrace {m} (w z e l d n : Fin m) : Formula m := .ex
  (trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc (Fin.last m) n.castSucc)
def validBody {m} (w n : Fin m) : Formula (m+5) := trace w.castSucc.castSucc.castSucc.castSucc.castSucc
  (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc
  (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) n.castSucc.castSucc.castSucc.castSucc.castSucc
def valid {m} (w n : Fin m) : Formula m := .ex (.ex (.ex (.ex (.ex (validBody w n)))))

theorem step_rename {m k} (w a b : Fin m) (r : Fin m → Fin k) : (step w a b).rename r = step (r w) (r a) (r b) := by
  simp only [step, Formula.rename, consCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem row_rename {m k} (w f i : Fin m) (r : Fin m → Fin k) : (row w f i).rename r = row (r w) (r f) (r i) := by
  simp only [row, rowWitness, Formula.rename, successor_rename, edge_rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem links_rename {m k} (w l f : Fin m) (r : Fin m → Fin k) : (links w l f).rename r = links (r w) (r l) (r f) := by
  simp only [links, Formula.rename, row_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem frame_rename {m k} (w z e l d f : Fin m) (r : Fin m → Fin k) :
    (frame w z e l d f).rename r = frame (r w) (r z) (r e) (r l) (r d) (r f) := by
  simp only [frame, Formula.rename, empty_rename, nilCode_rename, successor_rename, sequence_rename, edge_rename, links_rename]
theorem trace_rename {m k} (w z e l d f n : Fin m) (r : Fin m → Fin k) :
    (trace w z e l d f n).rename r = trace (r w) (r z) (r e) (r l) (r d) (r f) (r n) := by
  simp only [trace, Formula.rename, frame_rename, edge_rename]
theorem existsTrace_rename {m k} (w z e l d n : Fin m) (r : Fin m → Fin k) :
    (existsTrace w z e l d n).rename r = existsTrace (r w) (r z) (r e) (r l) (r d) (r n) := by
  simp only [existsTrace, Formula.rename, trace_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem valid_rename {m k} (w n : Fin m) (r : Fin m → Fin k) : (valid w n).rename r = valid (r w) (r n) := by
  simp only [valid, validBody, Formula.rename, trace_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_step {m} {Γ : Context m} (w a b h : Fin m) (hh : Derives Γ (.mem h w))
    (hc : Derives Γ (consCode w h a b)) : Derives Γ (step w a b) := by
  apply Derives.exI h
  simp only [Formula.instantiate, Formula.rename, consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hh hc

theorem intro_row {m} {Γ : Context m} (w f i j a b : Fin m) (hs : Derives Γ (successor j i))
    (ha : Derives Γ (edge f i a)) (hb : Derives Γ (edge f j b)) (hp : Derives Γ (step w a b)) : Derives Γ (row w f i) := by
  apply Derives.exI j
  apply Derives.exI a
  apply Derives.exI b
  simp only [Formula.instantiate, rowWitness, Formula.rename, successor_rename, edge_rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs (.conjI ha (.conjI hb hp))

theorem eliminate_row {m} {Γ : Context m} (w f i : Fin m) (r : Formula m) (hr : Derives Γ (row w f i))
    (hc : Derives (Context.add (rowWitness w f i) (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) r.raise.raise.raise) : Derives Γ r := by
  change Derives Γ (.ex (.ex (.ex _))) at hr
  apply Derives.exE hr
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, ⟨t, ht, he1⟩, he2⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ht, he1⟩, he2⟩

theorem links_at {m} {Γ : Context m} (w l f i : Fin m) (hl : Derives Γ (links w l f)) (hi : Derives Γ (.mem i l)) : Derives Γ (row w f i) := by
  have h : Derives Γ ((Formula.mem i l).imp (row w f i)) := by
    simpa only [links, Formula.instantiate, Formula.rename, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE i hl
  exact .impE h hi

theorem intro_trace {m} {Γ : Context m} (w z e l d f n : Fin m) (hz : Derives Γ (empty z)) (he : Derives Γ (nilCode w e))
    (hl : Derives Γ (.mem l w)) (hd : Derives Γ (successor d l)) (hf : Derives Γ (sequence f d w))
    (hseed : Derives Γ (edge f z e)) (hlinks : Derives Γ (links w l f)) (hn : Derives Γ (edge f l n)) : Derives Γ (trace w z e l d f n) :=
  .conjI (.conjI (.conjI hz he) (.conjI (.conjI hl hd) (.conjI hf (.conjI hseed hlinks)))) hn

theorem intro_existsTrace {m} {Γ : Context m} (w z e l d f n : Fin m) (hf : Derives Γ (trace w z e l d f n)) : Derives Γ (existsTrace w z e l d n) := by
  apply Derives.exI f
  simpa only [Formula.instantiate, trace_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf

theorem intro_valid {m} {Γ : Context m} (w n z e l d f : Fin m) (hf : Derives Γ (trace w z e l d f n)) : Derives Γ (valid w n) := by
  apply Derives.exI z
  apply Derives.exI e
  apply Derives.exI l
  apply Derives.exI d
  apply Derives.exI f
  simpa only [Formula.instantiate, validBody, Formula.rename, trace_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf

theorem eliminate_valid {m} {Γ : Context m} (w n : Fin m) (r : Formula m) (hv : Derives Γ (valid w n))
    (hc : Derives (Context.add (validBody w n) (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))))
      r.raise.raise.raise.raise.raise) : Derives Γ r := by
  change Derives Γ (.ex (.ex (.ex (.ex (.ex _))))) at hv
  apply Derives.exE hv
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, ⟨t, ⟨u, ⟨v, hv, h1⟩, h2⟩, h3⟩, h4⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ⟨u, Or.inr ⟨v, Or.inr hv, h1⟩, h2⟩, h3⟩, h4⟩

theorem under_five {m} {Γ : Context m} {r : Formula m} (hr : Derives Γ r) (b : Formula (m+5)) :
    Derives (Context.add b (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))) r.raise.raise.raise.raise.raise :=
  add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hr))))) b

theorem zf_under_five {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Formula (m+5)) :
    ZFContext.Evidence (Context.add b (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))) :=
  ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) b

theorem output_subst {m} {Γ : Context m} (w n p : Fin m) (he : Derives Γ (.equal n p)) (hn : Derives Γ (valid w n)) : Derives Γ (valid w p) := by
  have hi : Derives Γ ((valid w.castSucc (Fin.last m)).instantiate n) := by
    simpa only [Formula.instantiate, valid_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hn
  have ho := Derives.eqSubst (valid w.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, valid_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.StructuralListTraceSyntax
