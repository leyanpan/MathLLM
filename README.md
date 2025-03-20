# Lean Verification of LLM Mathematical Reasoning
This project aims to verify the natural language (NL) reasoning steps of Large Language models by generating LEAN proof for each NL reasoning step. The Lean verfication feedback will act as an "process supervision" feedback: if the model makes an incorrect step, the model will retry starting from the wrong step. This ensures that the model does not hallucinate at an intermediate step and resulting in an ultimatelly incorrect answer or proof.

# Example
For example, given the question:
```
Let $x$, $y$, and $z$ all exceed $1$ and let $w$ be a positive number such that $\\log_x w = 24$, $\\log_y w = 40$, and $\\log_{xyz} w = 12$. Find $\\log_z w$.
```

A NL reasoning model might generate the following:

```
Step 1:
We are given the following:
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
\log_x w = 24 \implies \frac{\ln w}{\ln x} = 24 \implies \ln w = 24 \ln x
\]
\[
\log_y w = 40 \implies \frac{\ln w}{\ln y} = 40 \implies \ln w = 40 \ln y
\]
\[
\log_{xyz} w = 12 \implies \frac{\ln w}{\ln (xyz)} = 12 \implies \ln w = 12 \ln (xyz)
\]

Step 2:
Expand \(\ln (xyz)\) using the property of logarithms:
\[
\ln (xyz) = \ln x + \ln y + \ln z
\]

Step 3:
Thus, the equation \(\ln w = 12 \ln (xyz)\) becomes:
\[
\ln w = 12 (\ln x + \ln y + \ln z)
\]
```

We want to formally verify the generate proof and each step. Specifically, we formalize the problem into a statement such as follows:
``` lean
/- Let $x$, $y$, and $z$ all exceed $1$ and let $w$ be a positive number such that $\log_x w = 24$, $\log_y w = 40$, and $\log_{xyz} w = 12$. Find $\log_z w$. -/
theorem problem (hx : x > 1) (hy : y > 1) (hz : z > 1) (hw : w > 0)
  (h1 : log w / log x = 24)
  (h2 : log w / log y = 40)
  (h3 : log w / log (x * y * z) = 12) :
  log w / log z = 60 := by sorry
```

Then each step of the proof will be formalized into

# Current Process Design
We tried using DeepSeek-Prover-V1.5-SFT, an dedicated LEAN proof LLM, but found that it has sub-par performance and does not handle instructions well. Therefore, we currently would like to use a general-purpose LLM to handle NL reasoning, translation to LEAN, and LEAN proof generation
1. LLM generates an NL solution for the problem as well as reasoning steps.
2. LLM generates a LEAN proof sketch, which includes the theorem statement, have statements, and NL comments preceeding each have step. The proof for each step and the final theorem statement is left as `sorry`.
3. The proof is loaded into PyPantograph, an interactive Lean proof environment, where the user can interact with the proof and provide feedback. PyPantograph will create a goal for each "sorry" in the proof. Each goal is matched with one of the original NL reasoning steps.
    * All comments should be stripped before passing to PyPantograph
4. A formal prover tries to close each goal by interacting with PyPantograph.
    * The prover is a LLM paired with a premise retriver (currently "https://premise-search.com/api/"). The premise retriever takes in a goal and returns the most relevant theorems/lemmas from Mathlib that helps close the current goal
    * An LLM is prompted with the proof prefix (i.e. the proof up to the current goal), the goal, and the retrieved premises. The LLM generates a proof for the current goal by using a series of tactics.
    * Use PyPantograph to see whether the tactic sequences proves the goal by passing the tactics one-by-one. If not, find the last tactic that is correct, get the proof, prefix, and premises at this point and repeat the process.
    * The above search process is reapeated for up to a certain threshold. If the prover fails, then we determine that the corresponding NL step is incorrect.
5. If the prover fails, the LLM generates a new proof starting from the incorrect step. We then repeat the above steps for the newly generated proof steps.

# Files
config.template.json: A template for the configuration file, including API keys. Should be copied to config.json and filled in with the correct API keys.

dsp_verify.py: A playground for demonstrating the usage of PyPanograph and the premise retriever.

lean_composer.py: A class that parses lean proofs.

prompts.py: includes all prompts for LLM calling.

dsp.py: The full pipeline for step-wise verification. Still work in progress

examples/sketch.lean: An example of a proof sketch that will be passed to PyPantograph, mainly used in dsp_verify.py
