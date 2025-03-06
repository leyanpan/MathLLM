from lean_composer import LeanComposer, ThmComposer

def incremental_formalization(question: str, formal_statement: str, nl_steps: list) -> LeanComposer:
    """
    Incrementally formalize an informal math problem and its reasoning steps.

    Parameters:
      question: The math problem, in natural language.
      nl_steps: A list of natural language reasoning steps.

    Returns:
      A LeanComposer object with prelims, an answer definition, and a theorem.

    Assumes:
      FRM_complete(prefix: str) -> str
        A function that takes a prefix (including any natural language comment)
        and returns a completed formal proof fragment in LEAN.
    """
    # Define the preliminaries and answer definition.
    prelims = "import Mathlib\n\nopen Real"
    answer_def = "def ans : ℕ := sorry"  # Adjust type as needed.

    # Build the initial formal theorem header.
    # We embed the informal math question as a comment.
    theorem_prefix = f"/- {question} -/\n" \
                     "theorem problem : Prop := by"
    # Call the FRM to complete the theorem header and initial proof block.
    formal_theorem = FRM_complete(theorem_prefix)

    # Create the top-level theorem using the FRM output.
    theorem_obj = ThmComposer(
        informal=question,
        statement=formal_theorem,
        steps=[],
        proof="sorry",  # This might be replaced after all steps are appended.
        indent=2
    )

    # Initialize the context with the formal theorem header.
    context = formal_theorem

    # Process each natural language step incrementally.
    for step in nl_steps:
        # The prefix combines the current context and the new step (as an informal comment).
        step_prefix = f"{context}\n/- {step} -/\n"
        # FRM_complete returns a formalized step: we assume the first line is the formal header,
        # and the subsequent lines are the corresponding proof.
        formal_step = FRM_complete(step_prefix)
        formal_lines = formal_step.splitlines()
        if not formal_lines:
            continue
        # Create a formal step object.
        step_obj = ThmComposer(
            informal=step,
            statement=formal_lines[0].strip(),  # first line: formal statement (e.g., "have ..." or "let ...")
            steps=[],  # For simplicity, no nested sub-steps in this example.
            proof="\n".join(formal_lines[1:]).strip(),  # rest of the lines: the step’s proof.
            indent=2
        )
        # Append the formal step to the theorem's list of steps.
        theorem_obj.steps.append(step_obj)
        # Update the context so that subsequent steps build on all previous formalizations.
        context += "\n" + formal_step

    # Finally, assemble the complete LeanComposer structure.
    lean_comp = LeanComposer(
        prelims=prelims,
        answer_def=answer_def,
        theorem=theorem_obj
    )

    return lean_comp