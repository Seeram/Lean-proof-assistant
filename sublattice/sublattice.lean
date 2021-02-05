import tactic
import order

-- sublattice zatial nie je definovane v mathlib
-- urobime to analogicky ako je definovany submonoid, subgroup

structure sublattice (L: Type*) [lattice L] :=
  (carrier : set L)
  (inf_mem  {a b: L} : a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier)
  (sup_mem  {a b: L} : a ∈ carrier → b ∈ carrier → a ⊔ b ∈ carrier)

-- kladne prirodzene cisla tvoria podzvaz ℕ
def poset_nat : sublattice ℕ :=
  { carrier := {n : ℕ | 1 ≤ n},
    inf_mem :=
      begin 
        intro a,
        intro b,
        intro a_set,
        intro b_set,
        simp at a_set, -- tuto nabehne simplifikacny mechanizmus
        simp at b_set,
        simp, -- tuto nabehol aj nejaky simplifikacny mechanizmus pre ⊓ !
        split,
        exact a_set,
        exact b_set,
      end,
    sup_mem := by finish, -- automatika funguje, toto islo aj pri inf_mem
  }

#check poset_nat 

#check linear_order.le_total 1 2
#check lattice

-- parne cisla tvoria podzvaz ℕ
-- ale: "kazda podmnozina nejakeho
-- linear_order je podzvazom linear_order"
-- cize toto dolu sa da zovseobecnit na funkciu 
-- {α : Type}: α → set α → sublattice α [linear_order α]
-- v duchu interval_sublattice nizsie

def even_nat : sublattice ℕ :=
{
  carrier := {n : ℕ | even n},
  inf_mem := 
    begin
      intro a,
      intro b,
      intro a_set,
      intro b_set,
      simp at a_set,
      simp at b_set,
      simp,
      -- vyuzijem, ze to je linearne usporiadanie
      have ab_total := linear_order.le_total a b,
      cases ab_total,
      {
      have a_is_inf := inf_eq_left.mpr ab_total,
      rw a_is_inf,
      exact a_set,
      },
      {
      have b_is_inf := inf_eq_right.mpr ab_total,
      rw b_is_inf,
      exact b_set,
      }
  end,
  sup_mem :=
    begin
      intro a,
      intro b,
      intro a_set,
      intro b_set,
      simp at a_set,
      simp at b_set,
      simp,
      have ab_total := linear_order.le_total a b,
      cases ab_total,
      {
      have b_is_sup := sup_eq_right.mpr ab_total,
      rw b_is_sup,
      exact b_set,
      },
      {
      have a_is_sup := sup_eq_left.mpr ab_total,
      rw a_is_sup,
      exact a_set,
      },
      end
}

-- vyroba podzvazu ako uzavreteho intervalu (alebo prazdnej mnoziny)
def interval_sublattice (L: Type*) (a b:L) [lat: lattice L] : sublattice L :=
  {
    carrier := {x:L | a ≤ x ∧ x ≤ b },
    inf_mem := 
      begin -- toto sa da automaticky dokazat cez taktiku finish, ale ved ucime sa 
        intros x y,
        intro x_in_interval,
        intro y_in_interval,
        simp at x_in_interval,
        simp at y_in_interval,
        simp,
        split, 
        have a_lt_x := and.elim_left x_in_interval,
        have a_lt_y := and.elim_left y_in_interval,
        exact and.intro a_lt_x a_lt_y,
        have x_leq_b := and.elim_right x_in_interval,
        refine inf_le_left_of_le x_leq_b, -- library_search
      end,
    sup_mem := by finish, -- aj takto ide
  }

def one_to_five := interval_sublattice ℕ 1 5
def two_to_seven := interval_sublattice ℕ 2 7

#check one_to_five 

-- Zadanie: implementujte kus z toho, co je v mathlib
-- implemenovane pre submonoid, subgroup pre strukturu sublattice vyssie













