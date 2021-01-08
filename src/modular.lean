import tactic
-- import order (netreba)

universe u

class modular_lattice(α : Type u) extends lattice α :=
  (modular_law: ∀ (x u v : α ), (x ≤ u) → u ⊓ (v ⊔ x) = (u ⊓ v) ⊔ x )

theorem modular_lattice_isomorphism { α: Type u } [ modular_lattice α ] { u v w x y : α}: 
  x ≤ u →
  x ≥ v →
  x ≥ u ⊓ v →
  x ≤ u ⊔ v → 
  u ⊓ ( v ⊔ x ) = x ∧ (u ⊓ x) ⊔ v = x
  := 
  begin
    intros h1 h2 h3 h4,
    split,
    {
      rw modular_lattice.modular_law,
      exact sup_eq_right.mpr h3,
      exact h1
    },
    {
      rw inf_comm,
      rw ← modular_lattice.modular_law,
      exact inf_eq_left.mpr h4,
      exact h2
    }
  end


  




 




 








