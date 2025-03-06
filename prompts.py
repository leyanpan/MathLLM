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

SOLVE_MATH_PROBLEM_STEP = """Solve the math problem step by step. Whenever a step is finished, output a special delimiter </step> to indicate the end of the step.
Put the final answer in \\boxed{{}}.

Problem: {problem}"""

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

Think carefully about how to make he formalization be valid. Then, put your formalized lean code inside a lean code block.

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