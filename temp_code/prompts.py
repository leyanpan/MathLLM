STATE_TO_TACTIC_PROMPT = """You are a Lean 4 expert. Please provide a tactic or sequence of tactics to close the following goal. Output ONLY the tactic(s) separated by newlines inside a code block.

```
{}
```"""

STATE_AND_ERROR_TO_TACTIC_PROMPT = """You are a Lean 4 expert. I am in the middle of a Lean proof. I am trying to prove a goal, but I am running into an error. In the first block I have the tactic I attempted, and in the following block I have the exact error. Please correct the tactic or provide a sequence of corrected tactics to close the goal, given the error. Output ONLY a singular code block containing the valid sequence of tactics to prove the goal.

```lean
{}
```


ERROR:

```
{}
```"""



SOLVE_MATH_PROBLEM = """Solve the math problem step by step. Put the final answer in \\boxed{{}}.
Problem: {problem}"""

CONCEPT_SUMMARIZE_SINGLE = """Summarize the most important concept, idea, method, or strategy used in this answer.
The summary should be short (ideally one or a few words, at most a single sentence).
Provide the summary in <summary></summary> tags.

Problem: {problem}

Solution: {solution_text}"""

PROMPT_DIFFERENCE = """Given the following problem and two solutions, one correct and one wrong,
identify the key concept or idea that distinguishes the correct solution from the wrong one.
The concept should be short and generalizable (a word or short phrase).
Provide your answer in <concept></concept> tags.

Problem: {problem}

Correct Solution: {correct_solution_text}

Wrong Solution: {wrong_solution_text}"""

SOLVE_MATH_PROBLEM_STEP = """Solve the following math problem step by step. Whenever a step is finished, output a special delimiter </step> to indicate the end of the step. Do not output this delimiter other than when completing a step.
Put the final answer in \\boxed{{}}.

Problem: {problem}"""

AUTOFORMALIZE_STEP = """Please formalize the next proof step in Lean 4. The step should be in the form of a 'have' statement. The 'have' statement must have 'sorry' appended. The 'ans' is a placeholder holding the answer. Think carefully about how to make the formalization valid. Then, put your formalized lean code inside a lean code block. ONLY place the 'have' statement in your response, so that it may be cleanly appended to the proof.

PROOF:
{proof}

NEXT HAVE:
"""

AUTOFORMALIZE_STATEMENT = """Can you formalize the following problem statement into LEAN 4 code with "sorry", with the final answer being an "ans" placeholder?

You do not need to provide the full proof, just the formalization of the problem statement. Use "ans" as a placeholder for the final answer.

You should add the following exact line before the formalization and natural language problem statement:
``` lean
def ans : ℕ := sorry
```
and use "ans" as a placeholder for the final answer in the formalized problem statement.

The entire formalized statement should be a single theorem, followed by ":= by sorry" to indicate that the proof is not yet provided.

Right before the theorem, place the natural language problem statement as a comment.

Your formalization should include all necessary imports that allows the statement to be properly compiled.

Think carefully about how to make the formalization be valid. Then, put your formalized lean code inside a lean code block.

Example Problem:

Let $k, l > 0$ be parameters. The parabola $y = kx^2 - 2kx + l$ intersects the line $y = 4$ at two points $A$ and $B$. These points are distance 6 apart. What is the sum of the squares of the distances from $A$ and $B$ to the origin?

Example Formalization:
``` lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Set Real

variable {{ k l: ℝ }}
variable {{ A B : ℝ × ℝ}}

def parabola (k l x : ℝ) := k*x^2 - 2*k*x + l
def line (x : ℝ) := 4
def ans : ℝ := sorry


/- Let $k, l > 0$ be parameters. The parabola $y = kx^2 - 2kx + l$ intersects the line $y = 4$ at two points $A$ and $B$. These points are distance 6 apart. What is the sum of the squares of the distances from $A$ and $B$ to the origin? -/
theorem example_problem(h₁ : parabola k l A.1 = line A.1)
  (h₂ : parabola k l B.1 = line B.1)
  (h₃ : A.2 = line A.1)
  (h₄ : B.2 = line A.1)
  (h₅ : (A.1 - B.1)^2 + (A.2 - B.2)^2 = 6 ^ 2)
  (hₜ : k ≠ 0) :
  A.1^2 + A.2^2 + B.1^2 + B.2^2 = ans := by sorry
```

Problem:

{problem}

Formalization:
"""

# For Testing
EXAMPLE_AIME_PROBLEM = """Let $x$, $y$, and $z$ all exceed $1$ and let $w$ be a positive number such that $\\log_x w = 24$, $\\log_y w = 40$, and $\\log_{xyz} w = 12$. Find $\\log_z w$."""















STEPS_RAW_OLD="""I'll solve this problem step by step, following your instructions to use the delimiter </step> at the end of each step and to put the final answer in a boxed format.

Let's begin by recalling the logarithm properties I'll need:
- $\log_a(b) = \frac{\log_c(b)}{\log_c(a)}$ for any base $c$
- $\log_a(xy) = \log_a(x) + \log_a(y)$

Now I'll solve the problem.

Step 1: I'll write out what we know.
$\log_x w = 24$
$\log_y w = 40$
$\log_{xyz} w = 12$

We need to find $\log_z w$.
</step>

Step 2: Let's use a common base for these logarithms. I'll choose the natural logarithm (base $e$) and apply the first property.

$\log_x w = \frac{\ln w}{\ln x} = 24$
$\log_y w = \frac{\ln w}{\ln y} = 40$
$\log_{xyz} w = \frac{\ln w}{\ln(xyz)} = 12$
</step>

Step 3: From the first equation, I can express $\ln w$ in terms of $\ln x$.
$\frac{\ln w}{\ln x} = 24$
$\ln w = 24 \cdot \ln x$
</step>

Step 4: Similarly, from the second equation, I can express $\ln w$ in terms of $\ln y$.
$\frac{\ln w}{\ln y} = 40$
$\ln w = 40 \cdot \ln y$
</step>

Step 5: Since both expressions for $\ln w$ are equal, I can write:
$24 \cdot \ln x = 40 \cdot \ln y$
$\frac{\ln x}{\ln y} = \frac{40}{24} = \frac{5}{3}$
</step>

Step 6: Now let's work with the third equation.
$\log_{xyz} w = \frac{\ln w}{\ln(xyz)} = 12$
$\ln w = 12 \cdot \ln(xyz)$
$\ln w = 12 \cdot [\ln x + \ln y + \ln z]$ (using the property $\ln(abc) = \ln a + \ln b + \ln c$)
</step>

Step 7: I'll substitute the expression for $\ln w$ from Step 3.
$24 \cdot \ln x = 12 \cdot [\ln x + \ln y + \ln z]$
$24 \cdot \ln x = 12\ln x + 12\ln y + 12\ln z$
$12 \cdot \ln x = 12\ln y + 12\ln z$
$\ln x = \ln y + \ln z$
</step>

Step 8: From Step 5, I know that $\ln x = \frac{5}{3} \cdot \ln y$
Substituting this into the equation from Step 7:
$\frac{5}{3} \cdot \ln y = \ln y + \ln z$
$\frac{5}{3} \cdot \ln y - \ln y = \ln z$
$\frac{2}{3} \cdot \ln y = \ln z$
$\ln z = \frac{2}{3} \cdot \ln y$
</step>

Step 9: Let's find $\log_z w$ using the properties of logarithms.
$\log_z w = \frac{\ln w}{\ln z}$
</step>

Step 10: From Step 4, I know $\ln w = 40 \cdot \ln y$
From Step 8, I know $\ln z = \frac{2}{3} \cdot \ln y$

Substituting these into the expression for $\log_z w$:
$\log_z w = \frac{40 \cdot \ln y}{\frac{2}{3} \cdot \ln y} = 40 \cdot \frac{3}{2} = 60$
</step>

Therefore, $\log_z w = 60$

\\boxed{60}"""



formalize_step="""
You are a mathematical formalization expert. Provide valid Lean 4 tactics to solve the following goal in Lean 4. A natural language description of the step is provided, as well as the tactic state. Fill in the Lean 4 code.
/- NATURAL LANGUAGE
Equating the expressions for \(\ln w\):
\[
24 \ln x = 40 \ln y = 12 (\ln x + \ln y + \ln z)
\]
From \(24 \ln x = 12 (\ln x + \ln y + \ln z)\), we have:
\[
24 \ln x = 12 \ln x + 12 \ln y + 12 \ln z
\]
\[
12 \ln x = 12 \ln y + 12 \ln z
\]
\[
\ln x = \ln y + \ln z
\]
\[
\ln x - \ln z = \ln y
\]
Therefore:
\[
rac{\ln y}{\ln x - \ln z} = 1
\]

Now use \(40 \ln y = 12(\ln x + \ln y + \ln z)\):
\[
40 \ln y = 12 \ln x + 12 \ln y + 12 \ln z
\]
\[
28 \ln y = 12 \ln x + 12 \ln z
\]
\[
28 \ln y = 12 (\ln x + \ln z)
\]
-/
/- TACTIC STATE:
x y z w : ℝ
hx : x > 1
hy : y > 1
hz : z > 1
hw : w > 0
h1 : log w / log x = 24
h2 : log w / log y = 40
h3 : log w / log (x * y * z) = 12
hlnw : log w = 24 * log x
hlnw' : log w = 40 * log y
hlnw'' : log w = 12 * (log x + log y + log z)
⊢ log y = 12 / 28 * (log x + log z)
-/

LEAN CODE:
```lean4
have hxy : log x + log z = (28 / 12) * log y := by
"""



formal_raw="""/- Let $x$, $y$, and $z$ all exceed $1$ and let $w$ be a positive number such that $\\log_x w = 24$, $\\log_y w = 40$, and $\\log_{xyz} w = 12$. Find $\\log_z w$. -/
theorem problem (hx : x > 1) (hy : y > 1) (hz : z > 1) (hw : w > 0)
  (h1 : log w / log x = 24)
  (h2 : log w / log y = 40)
  (h3 : log w / log (x * y * z) = 12) :
  log w / log z = 60 := by
"""





STEPS_RAW="""We are given the following:
\[
\log_x w = 24
\]
\[
\log_y w = 40
\]
\[
\log_{xyz} w = 12
\]
Our goal is to find \(\log_z w\).

First, rewrite each logarithmic expression in terms of the natural logarithm (\(\ln\)):
\[
\log_x w = 24 \implies \\frac{\ln w}{\ln x} = 24 \implies \ln w = 24 \ln x
\]
</step>
\[
\log_y w = 40 \implies \\frac{\ln w}{\ln y} = 40 \implies \ln w = 40 \ln y
\]
</step>
\[
\log_{xyz} w = 12 \implies \\frac{\ln w}{\ln (xyz)} = 12 \implies \ln w = 12 \ln (xyz)
\]
Expand \(\ln (xyz)\) using the property of logarithms:
\[
\ln (xyz) = \ln x + \ln y + \ln z
\]
Thus, the equation \(\ln w = 12 \ln (xyz)\) becomes:
\[
\ln w = 12 (\ln x + \ln y + \ln z)
\]
</step>

Equating the expressions for \(\ln w\):
\[
24 \ln x = 40 \ln y = 12 (\ln x + \ln y + \ln z)
\]
From \(24 \ln x = 12 (\ln x + \ln y + \ln z)\), we have:
\[
24 \ln x = 12 \ln x + 12 \ln y + 12 \ln z
\]
\[
12 \ln x = 12 \ln y + 12 \ln z
\]
\[
\ln x = \ln y + \ln z
\]
\[
\ln x - \ln z = \ln y
\]
Therefore:
\[
\frac{\ln y}{\ln x - \ln z} = 1
\]

Now use \(40 \ln y = 12(\ln x + \ln y + \ln z)\):
\[
40 \ln y = 12 \ln x + 12 \ln y + 12 \ln z
\]
\[
28 \ln y = 12 \ln x + 12 \ln z
\]
\[
28 \ln y = 12 (\ln x + \ln z)
\]
</step>

Finally, solve for \(\log_z w\).

Since \(\ln x = \ln y + \ln z\), substitute into the expression \(\ln w = 24 \ln x\):
\[
\ln w = 24 (\ln y + \ln z)
\]

From \(\ln w = 40\ln y\), equate:
\[
24 (\ln y + \ln z) = 40 \ln y
\]
\[
24 \ln y + 24 \ln z = 40 \ln y
\]
\[
24 \ln z = 16 \ln y
\]
\[
\ln z = \\frac{2}{3} \ln y
\]

Now compute \(\log_z w\):
\[
\log_z w = \\frac{\ln w}{\ln z} = \\frac{40 \ln y}{\frac{2}{3} \ln y} = 40 \cdot \\frac{3}{2}
\]
\[
= 60
\]
</step>

Therefore, \(\log_z w = \\boxed{60}\)."""