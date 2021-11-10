import data.set
import  tactic.ring

namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric reflexive,
  assume prop prop1 prop2,
  cases prop with beta t,
  have prop3:= prop2 beta,
  have prop4:= prop1 prop3,
  have f:= prop4 prop3,
  exact f,  
end



/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example : symmetric r → transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold symmetric transitive reflexive asymmetric,
  assume s t r,
  assume x,


end





/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  intros s s1 s2,
  --unfold powerset,
  assume prop1,
  assume prop2,
  assume s12,
  assume s21,
  apply set.ext,
  assume beta,
  apply iff.intro,
  assume bs2,
  have a:= s12 bs2,
  exact a,
  assume bs1,
  have b:= s21 bs1,
  exact b,
end


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro n,
  ring,

end

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,

end

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  assume n,
  unfold reflexive divides,
  apply exists.intro 1,
  ring,

end 

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z prop prop1,
  apply exists.intro 1,
  ring,

  cases prop with k c,
  cases prop1 with k1 d,
  
  have k2: k = 1 :=sorry,
  have k3: k1 = 1 :=sorry,

  have prop:=d.symm,
  have prop1:=c.symm,
  have prop2:=k2.symm,
  have prop3:=k3.symm,

  rw <-prop,
  rw <-prop1,
  ring,

  rw <-prop2,
  rw <-prop3,
  ring,
end 

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/
example : symmetric divides :=
begin
  assume x y,
  unfold divides,
  assume a,
  apply exists.intro 1,
  ring,
  cases a with b prop,
  have prop1:=prop.symm,
  have b1: b = 1 :=sorry,
  have b2:=b1.symm,
  rw <-prop1,
  rw <-b2,
  ring,
end 

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric,
  assume x y,
  unfold divides,
  assume a b,
  cases a with k yeq,
  have eqy:=yeq.symm,
  have k1: k=1:=sorry,
  rw <-eqy,
  have k_1:=k1.symm,
  rw <-k_1,
  ring,
end


/- #5
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric,
  assume rxy,
  unfold irreflexive,
  assume b,
  assume rxx,
  have c:= rxy rxx,
  have f:= c rxx,
  exact f,
end

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  assume a b x y,
  assume rxy,
  assume ryx,
  have:= b 
  have
end

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume t
end


end relation
