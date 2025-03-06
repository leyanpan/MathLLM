from openai import OpenAI
import re
import math
import random

import prompts


# model = 'deepseek-reasoner'
model = 'gpt-4o'
if model.startswith('deepseek'):
    client = OpenAI(api_key="", base_url="https://api.deepseek.com")
else:
    client = OpenAI(api_key="")

def extract_answer_value(text):
    """Extracts numeric value from <answer> tags with robust parsing."""
    try:
        return float(re.search(r'\\boxed{\s*([+-]?\d*\.?\d+)}\s*', text).group(1))
    except (AttributeError, ValueError, TypeError):
        return None

def extract_steps(response_text):
    """
    Extracts stepwise solutions from the model's response using the </step> delimiter.
    Returns a list of individual steps in order.
    """
    steps = re.split(r'\s*</step>\s*', response_text.strip())  # Split on the delimiter
    return [step.strip() for step in steps if step.strip()]  # Remove empty entries

def solve_math_problem_stepwise(problem, tempurature=1):
    """
    Sends a math problem to the GPT-4o model and retrieves stepwise solutions.
    Uses the SOLVE_MATH_PROBLEM_STEP prompt to enforce structured step-by-step reasoning.
    """
    # Format the prompt with the given problem
    prompt = prompts.SOLVE_MATH_PROBLEM_STEP.format(problem=problem)

    # Query the model
    response = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": prompt}],
        temperature=1  # Lower temperature for more deterministic responses
    )

    # Extract response text
    response_text = response.choices[0].message.content
    return extract_steps(response_text)

def formalize_statement(problem):
    """
    Formalizes a given math problem statement into Lean code using the AUTOFORMALIZE_STATEMENT prompt.
    The final answer is replaced with an "ans" placeholder.
    """
    # Format the prompt with the given problem
    prompt = prompts.AUTOFORMALIZE_STATEMENT.format(problem=problem)

    # Query the model
    response = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": prompt}],
        temperature=0.7
    )

    # Extract response text
    response_text = response.choices[0].message.content
    # Extract LEAN code block
    lean_expression = re.search(r'```\s*lean(.*?)```', response_text, re.DOTALL)
    if lean_expression:
        return lean_expression.group(1).strip()
    else:
        print("Error: Could not extract Lean code block. Returning Full Expression.")
        return response_text.strip()


if __name__ == "__main__":
    problem_statement = prompts.EXAMPLE_AIME_PROBLEM
    steps = solve_math_problem_stepwise(problem_statement)

    print("Stepwise Solution:")
    for i, step in enumerate(steps, start=1):
        print(f"Step {i}: {step}")

    print("\nFormalized Statement:")
    print(formalize_statement(problem_statement))