import PPAC.Migration.MinimalInstances

/-! 从分离与正则公理证明全参数有界成员极小元模式，最终输出原核Derives。 -/
namespace PPAC.Migration.BoundedMinimal
open Source SourceAlgebra SourceLogic MinimalPredicates MinimalLogic MinimalInstances
open ReplacementPredicates (paramsUp)

theorem minimal_exists {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation p).rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (he : Derives Γ (has p ρ a)) : Derives Γ (minimalExists p ρ a) := by
  have hc := separation_instance p ρ a hs
  let C := separated p (paramsUp ρ) a.castSucc (Fin.last m)
  let Γc := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hc
  apply Derives.exE (p := C) hc
  have hs' : Derives Γc C := .hyp (Or.inl rfl)
  have hf' : Derives Γc (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf C
  have he' : Derives Γc (has p (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, has_rename] using under he C
  have hr := Derives.impE (foundation_instance (Fin.last m) hf')
    (separated_inhabited p (paramsUp ρ) a.castSucc (Fin.last m) hs' he')
  have hm := minimal_from_regular p (paramsUp ρ) a.castSucc (Fin.last m) hs' hr
  simpa only [Formula.raise, minimalExists_rename] using hm

/-- 每个外部矩阵索引产生一个完整纯对象闭句，所有参数及界集合均在句内量化。 -/
def sentence {n} (p : Formula (n+1)) : Source.Sentence :=
  (Formula.all ((has p Fin.castSucc (Fin.last n)).imp
    (minimalExists p Fin.castSucc (Fin.last n)))).close

def assumptions {n} (p : Formula (n+1)) : Theory :=
  fun q => q = Source.SetLanguage.foundation ∨ q = Source.SetLanguage.separation p

/-- 只使用原始Foundation及一个Separation实例的19规则证书。 -/
theorem source_minimal {n} (p : Formula (n+1)) :
    Derives ((assumptions p).at 0) (sentence p) := by
  apply close_derives
  apply Derives.allI
  rw [theory_at_raise]
  apply Derives.impI
  have hf : Derives ((assumptions p).at (n+1)) (Source.SetLanguage.foundation.rename Fin.elim0) :=
    .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Derives ((assumptions p).at (n+1)) ((Source.SetLanguage.separation p).rename Fin.elim0) :=
    .hyp ⟨_, Or.inr rfl, rfl⟩
  exact minimal_exists p Fin.castSucc (Fin.last n) (add hs _) (add hf _) (.hyp (Or.inl rfl))

/-- 两公理理论上的原Hilbert核证书；不假设秩函数或对象良基递归。 -/
theorem kernel_certificate {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory (assumptions p)) []
      (Translation.sentence (sentence p)) := TheoryTransport.sentence (source_minimal p)

/-- 源Replacement版ZF内的实际闭句证明；未调用Collection。 -/
theorem source_ZF_minimal {n} (p : Formula (n+1)) :
    Derives (Source.SetLanguage.ZF.at 0) (sentence p) := by
  refine Derives.weaken ?_ (source_minimal p)
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation p, rfl⟩

/-- 原YesMetaZFC的实际对象推导：任意带参数公式、任意界集合。 -/
theorem native_minimal {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence p)) := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := kernel_certificate p)
  rintro q ⟨r, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact ZFEquivalence.source_foundation
  · exact SeparationSyntax.source_separation p
end PPAC.Migration.BoundedMinimal
