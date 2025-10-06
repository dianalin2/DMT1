/- @@@
#1. Suppose P and Q are any propositions.

#1.A: State and prove the conjecture that,
*and* implies *equivalence*. In other words,
if for any propositions, X and Y, X ∧ Y is
true, then it must be that X ↔ Y is as well.
Call your theorem andImpEquiv.
@@@ -/

-- ANSWER
def andImpEquiv (pq: P ∧ Q) : (P ↔ Q) :=
  Iff.intro
    (fun _ : P => pq.right)
    (fun _ : Q => pq.left)

#check andImpEquiv

/- @@@
#2: Give the proof in #1 in English. To do this,
just explain clearly what assumptions you make or
use at each step and what inference rules you use
to make progress at each step. We get you started:

-- ANSWER
To prove this implication, we will assume that
the premise of P ∧ Q is true since we have a proof of P ∧ Q.
Assuming P ∧ Q is true implies that P and Q are true
individually. We can then use the introduction rule for
implies to show that if P is true, Q must be true. Likewise,
we can use the introduction rule for implies to show that
if Q is true, P must be true. Therefore, the implication holds
both ways, indicating that P holds true if and only if Q
holds true.
@@@ -/


/- @@@
#3: Use axiom declarations to represent this world.

- X is a proposition
- Y is a propostion
- X ∧ Y is true

Once you've done that, in a #check command, apply
the general theorem we just proved to prove that X
is equivalent to Y.

Do not just copy the proof. The whole point is to
reinforce the idea that one you've proved a theorem
you can use it (by applying it) to prove any special
case (here involving X and Y) of the general claim.
@@@ -/

-- ANSWER
axiom x : X
axiom y : Y
def xy : X ∧ Y := And.intro x y

#check andImpEquiv xy

/- @@@
#4: Something About False

Recall from class discussion that the proposition,
in Lean, called False, has no proofs at all. That
is what makes it false. Assuming that there is one
assumes something that's impossibile. The crucial
conclusion to draw is *not* that the impossible is
suddenly possible, but that the *assumption* itself
must be wrong. Therefore, if at any point in trying
to prove something we can derive a proof of False,
that means we're in a situation that can't actually
happen. So we really don't have to finish the proof!

For example, suppose  K is some unknown proposition.
When we say that (False → K) is true, we are *not*
saying that *K* is true; we're saying that once you
assume or can derive a proof of False, you know you
are in a case that can never happen, so you can just
"bail out" and not worry about constructing a proof
of K, no matter what proposition it is. The keyword
*nomatch* in Lean applied to any proof of false does
exactly bail one of of an impossible case.

Here's a formal proof of it. We assume K is any
proposition, then we prove False → K. To prove
this implication, we assume we're given f, a proof
of false. In any other situation, for *exFalsoK*
to be defined, we'd *have to* return some value of
type K. Here we don't even know what that type is.
And yet the function is well-defined, and as such
*proves* the implication, *False → K*. The trick
of course, is that as soon as we have a proof of
false in (or derivable given) our context, then we
can *bail out* and Lean will accept the definition.
Lean's *nomatch* contruct will bail you out as long
as it's applied to a proof of false, which is the
evidence Lean needs to know it's ok to accept the
definition.
@@@ -/

-- ANSWER
def exFalsoK : (False → K)
| f => nomatch f

#check exFalsoK

/- @@@
Why is it safe to accept tihs definition? What do we
know that's special about *exFalsoK* that makes it ok?

-- ANSWER
It is safe to accept this definition because False is never True.
Therefore, in any implication where False is the antecedent, the implication
always holds true because a false antecedent does not imply anything.

Additionally, because no proofs of False can be created (by the definition
of False), no proofs of K can be created by this definition of exFalsoK, making
exFalsoK safe.

@@@ -/


/- @@@
#5 In Lean, state and prove the proposition that is
P and Q are aribtrary propositions, then False *and*
P implies Q.
@@@-/

-- ANSWER
def falseAndPImpQ (P Q : Prop) : ((False ∧ P) → Q) :=
  fun f => nomatch f

/- @@@
Write a short paragraph stating the proposition to be
proved and the proof of it -- in English.
@@@ -/

-- ANSWER
/-
The proposition to be proved is that (False and P) implies Q.

Proof: We assume P and Q are any propositions, then we prove
(False ∧ P) → Q. Since no proofs exist for False, no proofs
exist for (False and P) by the definition of And. By the
definition of implication, any antecedent with no proofs
always results in a true implication because the antecedent
is impossible. Therefore, (False ∧ P) → Q.
-/

/- @@@
#6 State and prove the proposition that False → False.
Give both formal and English (natural language) proofs.
@@@ -/

-- ANSWER
/-
The proposition to be proved is False → False. No proofs
exist for False. By the definition of implication, any
antecedent with no proofs always results in a true
implication because the antecedent is impossible. Therefore,
False → False.
-/
def falseImpFalse : False → False
| f => nomatch f

#check falseImpFalse
