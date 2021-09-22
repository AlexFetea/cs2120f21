/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _  -- trick question? why?

--Their is no intro rule for false.

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
    assume P, 
  apply iff.intro _ _,
  -- forward
    assume prop,
    apply or.elim prop,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end
/- For problem 1, we start by using the introduction
rule for if and only if, giving us two different
propositions. We use the elimination rule to show 
that P ∨ P implies P. Next we use the introduction
rule to show that P implies P ∨ P-/



example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
   assume prop,
    apply and.elim prop,
    assume p,
    assume p,
    exact p,
    assume prop,
    apply and.intro _ _,
    apply prop,
    apply prop,
end
/- For problem 2, we start by using the introduction
rule for if and only if, giving us two different
propositions. We use the elimination rule to show 
that P ∧ P implies P. Next we use the introduction
rule to show that P implies P ∧ P-/



example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
assume P Q,
apply iff.intro _ _,

assume prop,
apply or.elim prop,
assume p,
apply or.intro_right,
exact p,
assume q,
apply or.intro_left,
exact q,

assume prop,
apply or.elim prop,
assume p,
apply or.intro_right,
exact p,
assume q,
apply or.intro_left,
exact q,
end
/- For problem 3, we start by using the introduction
rule for if and only if, giving us two different
propositions. We use the elimination rule giving us 
the propositions P → Q ∨ P and Q → Q ∨ P. We use the
intro rule for or to prove the first proposition, and 
then use it again to prove the second proposition. To
solve backwards, we first apply the elimination rule 
for or, giving us Q → P ∨ Q and P → P ∨ Q, and then we
apply the intro rule for or to both propositions-/



example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,

  assume prop,
  apply and.elim prop,
  assume p,
  assume q,
  apply and.intro _ _,
  exact q,
  exact p,

  assume prop,
  apply and.elim prop,
  assume q,
  assume p,
  apply and.intro _ _,
  exact p,
  exact q,
end
/- For problem 4, we start by using the introduction
rule for if and only if. We then apply the elimination
rule for and, giving us P → Q → Q ∧ P. We then apply
the intro rule for and. Solving backwords, we apply the
elimination rule for and, giving us Q → P → P ∧ Q. We 
then use the introduction rule for and.-/



example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
assume P Q R,
apply iff.intro _ _,

assume prop,
apply and.elim prop,
assume p,
assume prop2,
apply or.elim prop2,
assume q,
apply or.intro_left,
apply and.intro _ _,
exact p,
exact q,
assume r,
apply or.intro_right,
apply and.intro _ _,
exact p,
exact r,

assume prop,
apply or.elim prop,
assume prop2,
apply and.elim prop2,
assume p,
assume q,
apply and.intro _ _,
exact p,
apply or.intro_left,
exact q,

assume prop3,
apply and.elim prop3,
assume p,
assume r,
apply and.intro _ _,
exact p,
apply or.intro_right,
exact r,
end
/- For problem 5, we start by using the introduction
rule for if and only if. We then apply the elimination
rule for and, giving us P → Q ∨ R → P ∧ Q ∨ P ∧ R. We 
then apply the elimination rule for or, giving us 
Q → P ∧ Q ∨ P ∧ R and R → P ∧ Q ∨ P ∧ R. intro rule for
and. We then apply the introrule for or, followed by the
intro rule for and, solving the firstproposition. We
apply the intro rule for or, followed by the intro rule
for and again, solving the seond propositions. Solving 
backwords, we apply the elimination rule for or, then the
elimination rule for and, giving us the proposition
P → Q → P ∧ (Q ∨ R). We then apply the intro rule for and
and the intro rule for or, solving the proposition. Next,
we apply the elimination rule for and, giving us the
proposition P → R → P ∧ (Q ∨ R). We finally apply the intro
rule for and, then the intro rule for or. -/



example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,

  assume prop,
  apply or.elim prop,
  assume p,
  apply and.intro,
  apply or.intro_left,
  exact p,
  apply or.intro_left,
  exact p,
  assume prop2,
  apply and.elim prop2,
  assume q,
  assume r,
  apply and.intro,
  apply or.intro_right,
  exact q,
  apply or.intro_right,
  exact r,

  assume prop,
  have pq :(P ∨ Q) := and.elim_left prop,
  have pr :(P ∨ R) := and.elim_right prop,
  apply or.elim pq,
  assume p,
  apply or.intro_left,
  exact p,
  assume q,
  apply or.elim pr,
  assume p,
  apply or.intro_left,
  exact p,
  assume r,
  apply or.intro_right,
  apply and.intro,
  exact q,
  exact r,
end
/- For problem 6, we start by using the introduction
rule for if and only if. We then apply the elimination
rule for and, giving us P → (P ∨ Q) ∧ (P ∨ R). We then
apply the intro rule for and to serperate the left and 
right statements. Each statement is then proven with the
intro rule for or. We use the eliminiation rule for or
to get Q → R → (P ∨ Q) ∧ (P ∨ R). We then apply the intro
rule for and, to seperate the statements. We then apply
the intro rule for or to each of these statements.
Solving backwords, we let pq represent the left half of
proposition using the elimination rule, and pr to 
represent the right have. using the elimination rule for
or on pq we are left with the statement P → P ∨ Q ∧ R. We
can then apply the intro rule for or to seperate the two
statements, followed by the intro rule for and to solve
the statement on the right.-/



example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume prop,
  apply and.elim prop,
  assume p,
  assume prop2,
  exact p,
  assume p,
  apply and.intro _ _,
  exact p,
  apply or.intro_left,
  exact p,
end
/- For problem 7, we start by using the introduction
rule for if and only if. We then apply the elimination
rule for and, giving us P ∧ (P ∨ Q) → P. We then
apply the elimination rule for and to serperate the left and 
right statements. We then use the intro rule for and to 
the left half of the proposition, and then apply the intro
rule for or to solve the right half.-/



example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume prop,
  apply or.elim prop,
  assume p,
  exact p,
  assume prop2,
  apply and.elim prop2,
  assume p,
  assume q,
  exact p,
  assume p,
  apply or.intro_left,
  exact p,
end
/- For problem 8, we start by using the introduction
rule for if and only if. We then apply the elimination
rule for or, giving us P ∧ (P ∨ Q) → P. We then
apply the elimination rule for and to serperate the left and 
right statements. We then apply the elimination rule for and
to seperate teh left and right statements. We finally apply 
the intro rule for or to solve the proposition.-/



example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  exact true.intro,
  assume t,
  apply or.intro_right,
  exact t,
end
/- For problem 8, we start by using the introduction
rule for if and only if. We use the intro rule for 
true to prov the first proposition. We use the intro
rule for or to prove the statement or the right hand
side true.-/



example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  apply or.elim prop,
  assume p,
  exact p,
  apply false.elim,
  assume p,
  apply or.intro_left,
  exact p, 
end
/- For problem 9, we start by using the introduction
rule for if and only if. We then apply the elimination
rule for or. We then apply the elimination rule for
false, proving one of the statements. We finally apply
the intro rule for or, proving the left hand side.-/

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  apply and.elim prop,
  assume p,
  assume t,
  exact p,
  
  assume p,
  apply and.intro,
  exact p,
  exact true.intro,
end
/- For problem 10, we start by using the introduction
rule for if and only if. We then apply the elimination
rule for and to solve the first proposition. We then use
the introduction rule for and followed by the introduction
rule for true to solve the second proposition.-/



example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  apply and.elim prop,
  assume p,
  assume f,
  exact f,
  apply false.elim,
end
/- For problem 11, we start by using the introduction
rule for if and only if. We then apply the elimination
rule for and to solve the first proposition. We then use
the elimination rule for flase to solve the second 
proposition.-/


