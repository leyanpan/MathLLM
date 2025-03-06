import re
from typing import List, Self, Optional, Tuple
from dataclasses import dataclass, field
import json

def indent(text, spaces=2):
    """
    Indents each line of the given text by the specified number of spaces.
    """
    return '\n'.join([' ' * spaces + line for line in text.split('\n')])

def comment(text):
    """
    Adds a comment to the Lean code. Each line is appended with spaces to align with Lean indentation.
    """
    return '/- ' + text + ' -/'

@dataclass
class ThmComposer:
    # Informal statement
    informal: Optional[str] = None
    # Formal statement
    statement: str = None
    # Intermediate steps that uses "have" or "let" etc, which have their own proofs
    steps: List[Self] = field(default_factory=list)
    # The final proof of the theorem, after all the steps
    proof: str = 'sorry'
    # number of indentation spaces before each line
    indent: int = 2

    def get_name(self):
        name_regex = re.compile(r'[theorem|lemma|have|let]\s+(.*?)\s+')
        name_match = name_regex.match(self.statement)
        if name_match:
            return name_match.group(1)
        else:
            return None

    def __str__(self):
        ret = ''
        if self.informal:
            ret += comment(self.informal) + '\n'
        ret += self.statement + '\n'
        for step in self.steps:
            ret += indent(str(step), self.indent) + '\n'
        ret += indent(self.proof, self.indent) + '\n'
        return ret

@dataclass
class LeanComposer:
    prelims: str
    answer_def: str
    theorem: ThmComposer

    def _parse_lean_code(self, lean_code):
        """
        Parses the given Lean theorem formalization into:
        - prelims: Import statements, comments, and other metadata
        - answer_def: The "def ans" statement defining the answer
        - theorem_statement: The theorem and proof skeleton
        """
        # Match answer definition (e.g., "def ans : ℕ := sorry")
        answer_match = re.search(r"def\s+ans\s*:\s*([\w\s]*)\s*:=\s*.*", lean_code)

        if answer_match:
            answer_def = answer_match.group(0)
            answer_type = answer_match.group(1).strip()
        else:
            answer_def = ""
            answer_type = "ℕ"  # Default to natural numbers

        # Match theorem statement (from "theorem ..." up to ":= by")
        theorem_match = re.search(r"(theorem .*?:=[\s\n]*by)", lean_code, re.DOTALL)

        if theorem_match:
            theorem_statement = theorem_match.group(1).strip()
        else:
            raise ValueError("Could not find theorem statement.")

        # Extract prelims (everything before the answer definition)
        prelims = lean_code.split(answer_def)[0].strip()

        return prelims, answer_def, theorem_statement


    def replace_answer_value(self, new_value):
        """
        Replaces the answer placeholder (e.g., `def ans : ℕ := sorry`) with a new value.
        """
        self.answer_def = re.sub(r":=.*", f":= {new_value}", self.answer_def)

    def insert_proof_steps(self, proof_steps):
        """
        Inserts proof steps into the theorem.
        Proof steps should be provided as a list of tuples (natural_language, lean_statement).

        Example:
        proof_steps = [
            ("First, we rewrite the logarithm equation in terms of log properties.",
             "have h_rewrite : log w = 24 * log x, by algebra"),
            ("Next, we express log w in terms of log y.",
             "have h_y : log w = 40 * log y, by algebra")
        ]
        """
        proof_lines = ["begin"]

        for step in proof_steps:
            natural_text, lean_step = step
            proof_lines.append(f"  -- {natural_text}")
            proof_lines.append(f"  {lean_step}")

        proof_lines.append("end")  # Close Lean proof block

        # Replace the "by sorry" at the end of the theorem with the new proof
        self.theorem_statement = re.sub(r":=\s*by\s*sorry", ":=", self.theorem_statement) + "\n" + "\n".join(proof_lines)

    def __str__(self):
        """
        Reconstructs the full Lean code after modifications.
        """
        return f"{self.prelims}\n\n{self.answer_def}\n\n{self.theorem}\n"

def get_indent(line: str) -> int:
    """Return the number of leading spaces in a line."""
    return len(line) - len(line.lstrip(' '))

def parse_comment_block(lines: List[str], index: int) -> Tuple[str, int]:
    """
    Parse a comment block that starts with '/-' and ends with '-/'.
    Returns the comment content (without markers) and the new line index.
    """
    comment_lines = []
    line = lines[index].strip()
    if line.startswith("/-") and line.endswith("-/") and len(line) > 3:
        comment_lines.append(line[2:-2].strip())
        return "\n".join(comment_lines), index + 1
    else:
        comment_lines.append(line[2:].strip())
        index += 1
        while index < len(lines):
            line = lines[index].strip()
            if line.endswith("-/"):
                comment_lines.append(line[:-2].strip())
                index += 1
                break
            else:
                comment_lines.append(line)
                index += 1
        return "\n".join(comment_lines).strip(), index

def parse_step_block(lines: List[str], index: int, block_indent: int) -> Tuple[ThmComposer, int]:
    """
    Parse one step block at a given indent level.

    A step block includes any natural language comment (if present)
    immediately followed by a keyword line (e.g. "have ... := by").
    Its body (the proof text and any nested steps) is everything until the next
    line at the same indent that starts a comment block or keyword.
    """
    step = ThmComposer(indent=2)

    # Optionally capture a preceding comment block.
    if lines[index].strip().startswith("/-"):
        informal, index = parse_comment_block(lines, index)
        step.informal = informal
        # Skip blank lines
        while index < len(lines) and lines[index].strip() == "":
            index += 1

    # Now expect a step statement (line starting with a keyword) at block_indent.
    if index < len(lines) and get_indent(lines[index]) == block_indent and any(
        lines[index].strip().startswith(kw + " ") for kw in ("theorem", "lemma", "have", "let")
    ):
        step.statement = lines[index][block_indent:].rstrip()
        index += 1
    else:
        raise ValueError(f"Expected step statement with a keyword at indent {block_indent} (line {index})")

    # Gather the body of this step:
    # Everything (at a greater indent) until a new step starts at block_indent.
    body_lines = []
    while index < len(lines):
        if get_indent(lines[index]) <= block_indent:
            break
        body_lines.append(lines[index])
        index += 1
    # Now, if there is any body text, process it:
    if body_lines:
        # We assume the body lines are indented more than block_indent.
        body_indent = get_indent(body_lines[0])
        # Parse nested steps within the body (if any) and also collect remaining proof text.
        nested_steps, proof_text, _ = parse_proof_block(body_lines, 0, body_indent)
        step.steps = nested_steps
        if proof_text:
            step.proof = proof_text
    return step, index

def parse_proof_block(lines: List[str], index: int, block_indent: int) -> Tuple[List[ThmComposer], str, int]:
    """
    Parse a block of proof lines starting at a given indent.

    This function partitions the block into a list of step blocks and any leftover text.
    Any line at the given indent (after skipping blanks) that starts with a comment or
    a keyword signals the beginning of a new step.

    Returns a tuple of:
      - A list of parsed ThmComposer steps,
      - A string of any accumulated proof text that did not belong to a step,
      - The new index.
    """
    steps = []
    proof_lines = []

    # First, capture any leading proof text (if present) until the first step marker.
    while index < len(lines):
        if lines[index].strip() == "":
            proof_lines.append("")
            index += 1
            continue
        if get_indent(lines[index]) <= block_indent:
            break
        # Otherwise, this line is proof text.
        proof_lines.append(lines[index][block_indent:])
        index += 1

    # Then, parse step blocks as long as we see them at the current indent.
    while index < len(lines):
        # Skip blank lines.
        if lines[index].strip() == "":
            index += 1
            continue
        if get_indent(lines[index]) == block_indent and (
            lines[index].strip().startswith("/-") or
            any(lines[index].strip().startswith(kw + " ") for kw in ("theorem", "lemma", "have", "let"))
        ):
            step, index = parse_step_block(lines, index, block_indent)
            steps.append(step)
        else:
            # Any additional lines at a higher indent are considered part of the leftover proof text.
            proof_lines.append(lines[index][block_indent:])
            index += 1

    proof_text = "\n".join(proof_lines).strip()
    return steps, proof_text, index

def parse_theorem(lines: List[str], index: int) -> Tuple[ThmComposer, int]:
    """
    Parse the top-level theorem block.

    This function first checks for an optional preceding comment block (the informal statement),
    then reads the theorem (or lemma) header, and finally gathers the proof block.
    The proof block is partitioned into steps (if any) and any trailing proof text.
    """
    informal = None
    # Check for an optional comment block.
    if index < len(lines) and lines[index].strip().startswith("/-"):
        informal, index = parse_comment_block(lines, index)
        while index < len(lines) and lines[index].strip() == "":
            index += 1

    # Expect a theorem (or lemma) header.
    if index < len(lines) and (lines[index].strip().startswith("theorem") or lines[index].strip().startswith("lemma")):
        statement = lines[index].strip()
        theorem = ThmComposer(informal=informal, statement=statement, indent=2)
        index += 1
        while index < len(lines) and lines[index].strip() == "":
            index += 1
        # If there is a proof block (indented lines), parse it.
        if index < len(lines) and get_indent(lines[index]) > 0:
            block_indent = get_indent(lines[index])
            steps, proof_text, index = parse_proof_block(lines, index, block_indent)
            theorem.steps = steps
            if proof_text:
                theorem.proof = proof_text
        return theorem, index
    else:
        raise ValueError(f"Expected theorem statement at line {index}")

def parse_lean_code(lean_code: str) -> LeanComposer:
    """
    Given a Lean source code string, parse it into a LeanComposer object.

    This function:
      - Extracts the preliminaries (e.g. import/open statements),
      - Finds the answer definition (a line starting with "def ans"),
      - And then parses the theorem block (including its informal comment and steps).
    """
    lines = lean_code.splitlines()
    prelims_lines = []
    answer_def = ""
    theorem_obj = None
    i = 0
    # Gather preliminaries until we hit the answer definition.
    while i < len(lines):
        if lines[i].strip().startswith("def ans"):
            answer_def = lines[i].strip()
            i += 1
            break
        else:
            prelims_lines.append(lines[i])
            i += 1
    while i < len(lines) and lines[i].strip() == "":
        i += 1
    if i < len(lines):
        theorem_obj, i = parse_theorem(lines, i)
    return LeanComposer(
        prelims="\n".join(prelims_lines).strip(),
        answer_def=answer_def,
        theorem=theorem_obj
    )


if __name__ == "__main__":
    # Example Lean code with a theorem and nested steps
    lean_code_example = """import Mathlib

open Real

def ans : ℕ := sorry

/-
Problem: Let $x$, $y$, and $z$ all exceed $1$ and let $w$ be a positive number such that \\(\\log_x w = 24\\), \\(\\log_y w = 40\\), and \\(\\log_{xyz} w = 12\\). Find \\(\\log_z w\\).
-/

theorem problem (x y z w : ℝ) (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) (hw : 0 < w) (h1 : logb x w = 24) (h2 : logb y w = 40) (h3 : logb (x * y * z) w = 12) : logb z w = ans := by
  /-**Step 1: Express \\(w\\) in terms of \\(x\\), \\(y\\), and \\(z\\).**

  Using the definition of logarithms, we can write:
  \\[
  w = x^{24}
  \\]-/
  have hw : w = x^24 := by
    rw [<-h1, rpow_logb]
    <;> linarith

  have hw1 : w = y^40 := by
    rw [<-h2, rpow_logb]
    <;> linarith

  have hw2 : w = (x * y * z)^12 := by
    have hu: x * y * z > 1 := by
      apply mul_pos
      <;> apply mul_pos
      <;> linarith
    rw [<-h3, rpow_logb]

  sorry
"""

    # Parse the example Lean code:
    lc = parse_lean_code(lean_code_example)

    # For demonstration, print the parsed parts:
    # print("Prelims:")
    # print(lc.prelims)
    # print("\nAnswer Definition:")
    # print(lc.answer_def)
    # print("\nTheorem:")
    # print(f"\nInitial Informal Statement:{lc.theorem.informal}")
    # print(f"\nInitial Statement:{lc.theorem.statement}")
    # print("\nSteps:")
    # for step in lc.theorem.steps:
    #     print(step)
    # print("\nProof:")
    # print(lc.theorem.proof)

    print(json.dumps(lc, default=lambda o: o.__dict__, indent=2))