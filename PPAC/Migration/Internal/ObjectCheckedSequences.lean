import PPAC.Migration.Internal.ObjectSequences

/-! 每个任意参数行公式的完整轨迹组合模式，直接返回原核证书。 -/
namespace PPAC.Migration.Internal.ObjectCheckedSequences
open Source SourceAlgebra SourceLogic SequenceSyntax CheckedSequence

def assumptions : Theory := fun _ => False
def params {n k} : Fin n → Fin (n+k) := Fin.castAdd k
def slot {n k} (i : Fin k) : Fin (n+k) := ⟨n+i.val, by omega⟩

def appendSentence {n} (p : Formula (n+2)) : Source.Sentence :=
  let ρ := params (n := n) (k := 6)
  let g := slot (n := n) (0 : Fin 6)
  let k := slot (n := n) (1 : Fin 6)
  let f := slot (n := n) (2 : Fin 6)
  let d := slot (n := n) (3 : Fin 6)
  let y := slot (n := n) (4 : Fin 6)
  let b := slot (n := n) (5 : Fin 6)
  ((checked p ρ f d b).imp ((ReplacementPredicates.rel p ρ d y).imp
    ((append g k f d y b).imp (checked p ρ g k b)))).close

def prefixSentence {n} (p : Formula (n+2)) : Source.Sentence :=
  let ρ := params (n := n) (k := 5)
  let g := slot (n := n) (0 : Fin 5)
  let f := slot (n := n) (1 : Fin 5)
  let d := slot (n := n) (2 : Fin 5)
  let k := slot (n := n) (3 : Fin 5)
  let b := slot (n := n) (4 : Fin 5)
  ((checked p ρ f d b).imp ((SequencePrefix.witness g f k b).imp (checked p ρ g k b))).close

theorem source_append {n} (p : Formula (n+2)) : Derives (assumptions.at 0) (appendSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact append_checked p params (slot (n := n) (0 : Fin 6)) (slot (n := n) (1 : Fin 6))
    (slot (n := n) (2 : Fin 6)) (slot (n := n) (3 : Fin 6)) (slot (n := n) (4 : Fin 6)) (slot (n := n) (5 : Fin 6))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_prefix {n} (p : Formula (n+2)) : Derives (assumptions.at 0) (prefixSentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact prefix_checked p params (slot (n := n) (0 : Fin 5)) (slot (n := n) (1 : Fin 5))
    (slot (n := n) (2 : Fin 5)) (slot (n := n) (3 : Fin 5)) (slot (n := n) (4 : Fin 5))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨s, hs, _⟩
  exact False.elim hs

theorem native_replay {p : YesMetaZFC.Logic.FirstOrder.Sentence ℒ}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) [] p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨s, hs, _⟩
  exact False.elim hs


theorem append_kernel_certificate {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence (appendSentence p)) := TheoryTransport.sentence (source_append p)
theorem source_ZF_append {n} (p : Formula (n+2)) : Derives (Source.SetLanguage.ZF.at 0) (appendSentence p) := source_ZF_replay (source_append p)
theorem native_append {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (appendSentence p)) :=
  native_replay (append_kernel_certificate p)


theorem prefix_kernel_certificate {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence (prefixSentence p)) := TheoryTransport.sentence (source_prefix p)
theorem source_ZF_prefix {n} (p : Formula (n+2)) : Derives (Source.SetLanguage.ZF.at 0) (prefixSentence p) := source_ZF_replay (source_prefix p)
theorem native_prefix {n} (p : Formula (n+2)) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (prefixSentence p)) :=
  native_replay (prefix_kernel_certificate p)
end PPAC.Migration.Internal.ObjectCheckedSequences
