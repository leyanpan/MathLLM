from openai import OpenAI
import anthropic
import re
import math
import random

import prompts
from config_utils import get_api_key, load_config

from rich.console import Console
from rich.markdown import Markdown
from rich.live import Live

# Load config
try:
    config = load_config()
    model = config.get('default_model', 'gpt-4o')
except FileNotFoundError:
    model = 'gpt-4o'

# Initialize client based on model
if model.startswith('deepseek'):
    client = OpenAI(
        api_key=get_api_key('deepseek', config),
        base_url="https://api.deepseek.com"
    )
elif model.startswith('claude'):
    client = anthropic.Anthropic(
        api_key=get_api_key('anthropic', config)
    )
else:
    client = OpenAI(api_key=get_api_key('openai', config))

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

def solve_math_problem_stepwise(problem, temperature=1):
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
        temperature=temperature  # Lower temperature for more deterministic responses
    )

    # Extract response text
    response_text = response.choices[0].message.content
    #with open("prompts.py", "a") as file:
    #    file.write(response_text)  # Ensure newline if needed
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

def formalize_step(step, curr_proof):
    # Format the prompt with the given problem

    curr_proof = curr_proof + "\n/-\n" + step + "\n-/\n"
    #print(proof_with_step)

    prompt = prompts.AUTOFORMALIZE_STEP.format(proof=curr_proof)

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
        return curr_proof + lean_expression.group(1).strip()
    else:
        print("Error: Could not extract Lean code block. Returning Full Expression.")
        return response_text.strip()
print()

if __name__ == "__main__":
    problem_statement = prompts.EXAMPLE_AIME_PROBLEM
    print("PROBLEM STATEMENT: " + problem_statement)
    STEPS_RAW=prompts.STEPS_RAW
    steps = extract_steps(STEPS_RAW)
    print("Generating informal solution...")
    #steps=solve_math_problem_stepwise(problem_statement)

    print(steps)

    print("Stepwise Solution:")
    for i, step in enumerate(steps, start=1):
        print("########################################")
        print(f"{step}")
        print("########################################")

    print("\nFormalized Statement:")
    curr_proof=prompts.formal_raw
    print(curr_proof)

    for i, step in enumerate(steps, start=1):
        curr_proof = formalize_step(step, curr_proof) + "\n"
        print(curr_proof)

    md = Markdown("```lean4\n"+curr_proof+"```", code_theme="monokai")
    with Live(md, refresh_per_second=4) as live:
        live.update(md)


    write=True
    if write:
        with open("sketch.lean", "w") as file:
            file.write(curr_proof)  # Ensure newline if needed

