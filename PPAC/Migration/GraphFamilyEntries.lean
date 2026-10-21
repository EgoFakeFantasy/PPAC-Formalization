import PPAC.Migration.GraphFamilyValues

/-! 并图的每个成员仍是实际定义域内的有序对，保持原functionOn第一合取。 -/
namespace PPAC.Migration.GraphFamilyEntries
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic InsertSyntax
open GraphDomainSyntax GraphDomainBound GraphFamilySyntax OrderedPairElimination

theorem entry_domain {m} {Γ : Context m} (g d p e : Fin m)
    (hd : Derives Γ (domain d g)) (hp : Derives Γ (.mem p g)) (he : Derives Γ (entryOn e p)) :
    Derives Γ (entryOn d p) := by
  let B := entryWitnesses e p
  let Γb := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply entry_elim e p _ he
  have hdB : Derives Γb (domain d.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, domain_rename] using under_two hd B
  have hpB : Derives Γb (.mem p.castSucc.castSucc g.castSucc.castSucc) := under_two hp B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hEdge := edge_intro g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) p.castSucc.castSucc hpB (.conjR hB)
  have hx := Derives.impE (.conjR (domain_at d.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc hdB))
    (has_edge_intro _ _ _ hEdge)
  have hr := entry_intro d.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hx (.conjR hB)
  simpa only [Formula.raise, entryOn_rename] using hr

theorem member_entry {m} {Γ : Context m} (g d f p : Fin m)
    (hu : Derives Γ (unionOf g f)) (hd : Derives Γ (domain d g))
    (hf : Derives Γ (graphs f)) (hp : Derives Γ (.mem p g)) : Derives Γ (entryOn d p) := by
  have hh := Derives.impE (.conjL (union_at g f p hu)) hp
  let H := (Formula.mem (Fin.last m) f.castSucc).conj (.mem p.castSucc (Fin.last m))
  let Γh := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have resultH : Derives Γh (entryOn d.castSucc p.castSucc) := by
    have hfH : Derives Γh (graphs f.castSucc) := by
      simpa only [Formula.raise, graphs_rename] using under hf H
    have hdH : Derives Γh (domain d.castSucc g.castSucc) := by
      simpa only [Formula.raise, domain_rename] using under hd H
    have hpH : Derives Γh (.mem p.castSucc g.castSucc) := under hp H
    have hH : Derives Γh H := .hyp (Or.inl rfl)
    have he := Derives.impE (graphs_at f.castSucc (Fin.last m) hfH) (.conjL hH)
    let E := functionOn (Fin.last m).castSucc (Fin.last (m+1))
    let Γe := Context.add E (Context.image Formula.raise Γh)
    change Derives Γh (.ex E) at he
    apply Derives.exE (p := E) he
    have hdE : Derives Γe (domain d.castSucc.castSucc g.castSucc.castSucc) := by
      simpa only [Formula.raise, domain_rename] using under hdH E
    have hpE : Derives Γe (.mem p.castSucc.castSucc g.castSucc.castSucc) := under hpH E
    have hHE : Derives Γe ((Formula.mem (Fin.last m).castSucc f.castSucc.castSucc).conj
        (.mem p.castSucc.castSucc (Fin.last m).castSucc)) := by
      simpa only [Formula.raise, H, Formula.rename] using under hH E
    have hE : Derives Γe E := .hyp (Or.inl rfl)
    have hentry := Derives.impE (entries_at (Fin.last m).castSucc (Fin.last (m+1)) p.castSucc.castSucc (.conjL hE)) (.conjR hHE)
    have hr := entry_domain g.castSucc.castSucc d.castSucc.castSucc p.castSucc.castSucc (Fin.last (m+1)) hdE hpE hentry
    simpa only [Formula.raise, entryOn_rename] using hr
  simpa only [Formula.raise, entryOn_rename] using resultH

theorem entries_on {m} {Γ : Context m} (g d f : Fin m)
    (hu : Derives Γ (unionOf g f)) (hd : Derives Γ (domain d g)) (hf : Derives Γ (graphs f)) :
    Derives Γ (entriesOn g d) := by
  apply Derives.allI
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf g.castSucc f.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  have hd' : Derives (Context.image Formula.raise Γ) (domain d.castSucc g.castSucc) := by
    simpa only [Formula.raise, domain_rename] using Derives.rename Fin.castSucc hd
  have hf' : Derives (Context.image Formula.raise Γ) (graphs f.castSucc) := by
    simpa only [Formula.raise, graphs_rename] using Derives.rename Fin.castSucc hf
  apply Derives.impI
  exact member_entry g.castSucc d.castSucc f.castSucc (Fin.last m)
    (add hu' _) (add hd' _) (add hf' _) (.hyp (Or.inl rfl))
end PPAC.Migration.GraphFamilyEntries
