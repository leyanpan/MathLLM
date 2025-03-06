from openai import OpenAI
import re
import math
import random

import prompts

model = 'deepseek-reasoner'
# model = 'gpt-4o'
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

def generate_concept_summaries(problem, solution_text, generation_count=2):
    """
    Generate multiple concept summaries for a given solution.
    The prompt instructs the model to summarize the key idea in short text within <summary> tags.
    """
    response = client.chat.completions.create(
        model=model,
        messages=[
            {"role": "user", "content": (prompts.CONCEPT_SUMMARIZE_SINGLE.format(problem=problem, solution_text=solution_text))}
        ],
        n=generation_count,
        temperature=0.7
    )

    summaries = []
    for choice in response.choices:
        content = choice.message.content
        match = re.search(r'<summary>(.*?)</summary>', content, re.DOTALL)
        if match:
            summary = match.group(1).strip()
            # Split multi-concept summaries while preserving single concepts
            concepts = re.split(r'[;,]|\band\b', summary)
            summaries.extend([c.strip() for c in concepts if c.strip()])
    return summaries[:generation_count*2]  # Allow up to 2 concepts per generation

def generate_concept_difference(problem, correct_solution_text, wrong_solution_text, generation_count=2):
    """
    Generate a concept that differentiates the correct solution from the wrong solution.
    The prompt asks the model to identify a short, generalizable concept that distinguishes
    the correct answer from the wrong one. The answer is provided in <concept> </concept> tags.
    """
    response = client.chat.completions.create(
        model="gpt-4o",
        messages=[
            {"role": "user", "content": (prompts.PROMPT_DIFFERENCE.format(problem=problem,
                                                                          correct_solution_text=correct_solution_text,
                                                                          wrong_solution_text=wrong_solution_text))}
        ],
        n=generation_count,
        temperature=0.7
    )

    concepts = []
    for choice in response.choices:
        content = choice.message.content
        match = re.search(r'<concept>(.*?)</concept>', content, re.DOTALL)
        if match:
            concept = match.group(1).strip()
            # If multiple concepts are provided, split them
            split_concepts = re.split(r'[;,]|\band\b', concept)
            concepts.extend([c.strip() for c in split_concepts if c.strip()])
    return concepts[:generation_count]

def calculate_average_mdl(problem, correct_answer, num_samples=10, summaries_per_answer=2):
    """
    Generate multiple answers for the problem, calculate the average MDL (negative log probability)
    for correct answers, and produce a concept distribution as follows:
      - If both correct and wrong answers exist, a random correct/wrong pair is used to generate a concept
        via generate_concept_difference.
      - If all answers are correct, use the original generate_concept_summaries for each correct answer.
      - If all answers are wrong, do not return any concepts.
    """
    try:
        correct_value = float(correct_answer)
    except ValueError:
        raise ValueError("correct_answer must be numeric")

    # Generate multiple answers
    response = client.chat.completions.create(
        model="gpt-4o",
        messages=[
            {"role": "user", "content": (prompts.SOLVE_MATH_PROBLEM.format(problem=problem))}
        ],
        n=num_samples,
        logprobs=True,
        temperature=0.7
    )

    correct_mdls = []
    correct_solutions = []
    wrong_solutions = []

    # Process responses and separate correct and wrong solutions
    for choice in response.choices:
        content = choice.message.content
        print(content)
        answer = extract_answer_value(content)
        print(f"Answer: {answer}")
        print(f"Correct: {correct_value}")
        if answer is not None and math.isclose(answer, correct_value, abs_tol=1e-9):
            # Calculate MDL for the correct answer
            token_logprobs = [t.logprob for t in choice.logprobs.content]
            mdl = -sum(token_logprobs)
            correct_mdls.append(mdl)
            correct_solutions.append(content)
        else:
            wrong_solutions.append(content)

    # Determine concept generation strategy based on available responses
    concept_distribution = []
    if not correct_mdls:
        # All answers are wrong; do not return any concepts.
        avg_mdl = None
    else:
        avg_mdl = sum(correct_mdls) / len(correct_mdls)
        if wrong_solutions:
            # Both correct and wrong answers exist: pick one random pair.
            correct_choice = random.choice(correct_solutions)
            wrong_choice = random.choice(wrong_solutions)
            concepts = generate_concept_difference(problem, correct_choice, wrong_choice, generation_count=summaries_per_answer)
            # Mark each concept with a count of 1 since it's derived from a single pair.
            concept_distribution = [(concept, 1) for concept in concepts]
        else:
            # All answers are correct; use the original summarization.
            concept_counter = {}
            for sol in correct_solutions:
                concepts = generate_concept_summaries(problem, sol, generation_count=summaries_per_answer)
                for concept in concepts:
                    concept_counter[concept] = concept_counter.get(concept, 0) + 1
            concept_distribution = sorted(concept_counter.items(), key=lambda x: (-x[1], x[0]))

    return {
        'average_mdl_nats': avg_mdl,
        'average_mdl_bits': avg_mdl * 1.4427 if avg_mdl is not None else None,
        'correct_answers': len(correct_mdls),
        'total_samples': num_samples,
        'concept_distribution': concept_distribution
    }

# Usage example
result = calculate_average_mdl(
    problem=(prompts.EXAMPLE_AIME_PROBLEM),
    correct_answer=60,
    num_samples=10,
    summaries_per_answer=2
)

if result is not None:
    print(f"""Average MDL per correct answer: {result['average_mdl_nats']:.1f} nats ({result['average_mdl_bits']:.1f} bits)
Correct answers: {result['correct_answers']}/{result['total_samples']}

Most frequent concepts:""")
    for concept, count in result['concept_distribution'][:5]:
        print(f"- {concept} ({count} mentions)")
else:
    print("No correct answers were generated; no concept analysis available.")