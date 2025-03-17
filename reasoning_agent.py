# Reasoning agent from https://github.com/ag2ai/ag2/blob/main/autogen/agents/experimental/reasoning/reasoning_agent.py
# adapted to openai Agent
# Copyright (c) 2023 - 2025, AG2ai, Inc., AG2ai open-source projects maintainers and core contributors
#
# SPDX-License-Identifier: Apache-2.0
import math
import random
import re
import asyncio
from typing import NamedTuple, Any, Literal, Optional, Tuple
from agents import Agent, Runner, trace

from apis import get_chat_model

EPSILON = 1e-6

default_system = """
Develop a careful proof or disproof, or show no clear solution. Do not use code or numerics. Make sure all steps are fully justified. Do not do proofs by counterexample.
"""

TREEOFTHOUGHT_MESSAGE = """
Role: Expert Planning AI Assistant

Task: Given a question and a list of previous steps (the plan trajectory), generate at least four innovative options for the next step. The user would not answer you anything.

Instructions:
- Review the user's question and the previous steps taken.
- Identify any mistakes or errors in the previous steps.
- If you find any mistakes, include options to correct them in your proposed options.
- Think creatively to propose at least four possible options that logically build upon or correct the previous steps.
- Reply a single word 'TERMINATE' as an option if you believe the user's question is fully resolved.
- Provide a brief description for each option.
- Present your output in the specified format.
- If the question is a multi-choice question, you should carefully eliminate obviously wrong choices, look for contextual clues in the question, and use logical reasoning to select the most plausible answer.
- If you need to validate, simulate, or illustrate a reasoning concept with Python, place the code in a fenced block like ```python ... ``` and always print the results that you want to see.

(Note: Randomness, floating point precision, or hardware specifics may affect outputs, so your reasoning should not rely heavily on Python results.)

---

**Format of Output:**

REFLECTION:
*Give a few sentence reflections on the previous steps, what are wrong and what are good.*

**Possible Options:**
Option 1: Correct the error X in the previous steps.

Option 2: Reiterate and understand the user's question.

Option 3: Analyze and validate the results based on the previous steps.

Option 4: Perform Y.
"""

outcome_rating_prompt = """Please rate the answer on a scale of 1 to {rating_scale}, where 1 is the worst and {rating_scale} is the best.

A great answer must:
- Directly address the original question
- Be factually accurate and complete
- Show clear logical reasoning

Additionally, a good answer should:
- Be concise and well-structured
- Use appropriate language and tone
- Provide relevant examples or evidence when needed
- Be free of contradictions or inconsistencies

If the answer fails to meet any of the core requirements above, it should be considered a poor response.

Please provide your rating along with a brief explanation of your assessment.
"""

# Process Rating
scale_rating_prompt = """Please rate the thinking trajectory on a scale of 1 to {rating_scale}, where 1 is the worst and {rating_scale} is the best.

A great thinking trajectory must:
- Advance the process of solving the problem.

Additionally, a good trajectory should:
- Follow in clear logical steps.
- Contain no inaccuracies.
- Be free of any odd or irrelevant content.

If the trajectory does not meet one of the above requirements, it is considered a bad response.

Please provide your rating along with a brief explanation of your assessment.
"""

rewriter_message = """
Task: Given a list of messages including a previous discussion, write a prompt that summarizes the discussion, including all the useful information and intermediate steps, and asks a question.

**Messages:**
{messages}

**Format of Output:**
QUESTION: *Write the initial question asked by the user here.*
SUMMARY: *summarize the existing discussions.*

ACTIVITY LOG:
- *Action 1 performed*
- *Action 2 performed*
- ...

CURRENT_QUESTION: *Write the current/last question to be addressed here. In case the task has been completed, write: "The task has now been completed, write the final response and terminate the task."*
"""


class ThinkNode:
    depth: int  #: The depth of this node in the tree (root = 0).
    parent: Optional["ThinkNode"]
    children: list["ThinkNode"]
    content: str  # the text content/description for this reasoning step.
    value: float  # A numeric score/value assigned to this node.
    visits: int  # Number of times this node has been visited during search.
    reflection: str  # A string containing reflections on the reasoning process.
    rating_details: str  # A string providing details about the rating of this node.

    def __init__(self, content: str, parent: Optional["ThinkNode"] = None) -> None:
        """A node in a tree structure representing a step in the reasoning process.

        This class implements a tree node that stores content (text describing a reasoning step),
        maintains parent-child relationships, tracks node statistics, and provides utilities
        for traversing/visualizing the reasoning path.

        Args:
            content (str): The text content/description for this reasoning step.
            parent (Optional[ThinkNode]): The parent node in the tree, if any.

        The node automatically maintains the tree structure by:
        - Setting its depth based on the parent's depth + 1.
        - Adding itself to the parent's children list if the parent exists.
        - Providing trajectory utilities to get the full path from root to this node.
        """
        self.content: str = content
        self.value: float = 0.0
        self.parent: Optional[ThinkNode] = parent
        self.reflection: str = ""
        self.rating_details: str = ""
        self.depth: int = parent.depth + 1 if parent is not None else 0
        self.children: list[ThinkNode] = []
        self.visits: int = 0
        if self.parent:
            self.parent.children.append(self)

    @property
    def _trajectory_arr(self) -> list[str]:
        """Gets the full path from root to this node as a list of strings.

        Returns:
            list[str]: list containing the content of each node from root to current node
        """
        if self.parent:
            return self.parent._trajectory_arr + [self.content]
        return ["# Question:\n" + self.content + "\n---\n"]

    @property
    def trajectory(self) -> str:
        """Get a formatted string representation of the path from root to this node.

        Returns:
            str: A formatted string showing the question and each step in the reasoning process
        """
        traj = self._trajectory_arr
        ans = traj[0]
        for i, option in enumerate(traj[1:]):
            ans += f"\nStep {i + 1}: {option}"
        return ans

    def backpropagate(self, reward: float) -> None:
        """Update the score of this node and its parents using moving average.

        Args:
            reward (float): The reward to backpropagate up the tree.
        """
        node: Optional[ThinkNode] = self
        while node is not None:
            node.visits += 1
            node.value = (node.value * (node.visits - 1) + reward) / node.visits
            node = node.parent

    def __str__(self) -> str:
        return f"{self.content} -> Depth: {self.depth} Value: {self.value} Visits: {self.visits}"

    def __repr__(self) -> str:
        return self.__str__()

    def to_dict(self) -> dict[str, Any]:
        """Convert ThinkNode to dictionary representation.

        Returns:
            dict[str, Any]: dictionary containing all node attributes and recursive children
        """
        return {
            "content": self.content,
            "value": self.value,
            "depth": self.depth,
            "reflection": self.reflection,
            "rating_details": self.rating_details,
            "visits": self.visits,
            "children": [child.to_dict() for child in self.children],
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any], parent: Optional["ThinkNode"] = None) -> "ThinkNode":
        """Create ThinkNode from dictionary representation.

        Args:
            data (dict[str, Any]): dictionary containing node data
            parent (Optional[ThinkNode]): Parent node to attach to

        Returns:
            ThinkNode: Reconstructed node with all children
        """
        node = cls(content=data["content"], parent=parent)
        node.value = data["value"]
        node.depth = data["depth"]
        node.visits = data["visits"]
        node.reflection = data.get("reflection", "")
        node.rating_details = data.get("rating_details", "")

        # Recursively create children
        for child_data in data["children"]:
            cls.from_dict(child_data, parent=node)

        return node

    def visualize_tree(self, filename="tree_of_thoughts") -> None:
        """Visualize the tree of thoughts using graphviz."""
        from graphviz import Digraph

        dot = Digraph(comment="Tree of Thoughts")
        dot.attr(rankdir="TB")  # Top to Bottom direction

        def add_nodes(node: ThinkNode, node_id: str = "0") -> None:
            # Truncate long content for better visualization
            display_content = (node.content[:50] + "...") if len(node.content) > 50 else node.content

            # Add node with stats
            label = f"{display_content}\n visits: {node.visits}\n value: {node.value}"
            dot.node(node_id, label)

            # Recursively add children
            for i, child in enumerate(node.children):
                child_id = f"{node_id}_{i}"
                add_nodes(child, child_id)
                dot.edge(node_id, child_id)

        add_nodes(self)

        # Render the graph
        try:
            dot.render(filename, view=False, format="png", cleanup=True)
        except Exception as e:
            print(f"Error rendering graph: {e}")
            print("Make sure graphviz is installed on your system: https://graphviz.org/download/")


class Question(NamedTuple):
    node: ThinkNode
    agent: Agent
    prompt: str


def extract_sft_dataset(root: ThinkNode) -> list[dict[str, Any]]:
    """Extract the best trajectory or multiple equally good trajectories for SFT training.

    Args:
        root (ThinkNonde): The root node of the tree.

    Returns:
        list[dict]: list of best trajectories, each one is a pair of instruction and response.
    """
    instruction = root.content
    idx = len("# Question: ") + len(root.content) + 1

    def _find_leaf_nodes(node: ThinkNode) -> list[ThinkNode]:
        """Recursively find all leaf nodes."""
        if not node.children:
            return [node]
        leafs = []
        for child in node.children:
            leafs.extend(_find_leaf_nodes(child))
        return leafs

    # Step 1: Find all leaf nodes
    leaf_nodes = _find_leaf_nodes(root)

    # Step 2: Determine the highest score among leaf nodes
    max_value = max(leaf_nodes, key=lambda x: x.value).value

    # Step 3: Collect all leaf nodes with the highest score
    best_leafs = [leaf for leaf in leaf_nodes if leaf.value == max_value]

    # Step 4: Collect trajectories for all the best leaf nodes
    best_trajectories = [{"instruction": instruction, "response": leaf.trajectory[idx:]} for leaf in best_leafs]

    return best_trajectories


def extract_rlhf_preference_dataset(root: ThinkNode, contrastive_threshold: float = 0.2) -> list[dict[str, Any]]:
    """Extract and generate preference pairs for RLHF training by comparing sibling nodes.

    Args:
        root (ThinkNode): The root node of the tree.
        contrastive_threshold (float): between (0, 1), a distance measure that we are confident to call
            one is positive and another is negative.

    Returns:
        list[dict]: list of preference pairs, where each pair contains two responses and
        indicates which one is preferred.
    """
    preference_pairs = []

    assert contrastive_threshold > 0
    assert contrastive_threshold < 1

    def traverse_tree(node: ThinkNode) -> None:
        """Traverse the tree to compare sibling nodes and collect preferences."""
        if not node.children:
            return  # Leaf node, no comparisons needed

        # Step 1: Compare all sibling nodes
        for i in range(len(node.children)):
            for j in range(len(node.children)):
                if i == j:
                    continue
                child_a, child_b = node.children[i], node.children[j]

                is_a_better = False
                if child_a.visits > 0 and child_b.visits > 0:
                    # for MCTS
                    is_a_better = (
                            child_a.value / child_a.visits - child_b.value / child_b.visits > contrastive_threshold
                    )
                else:
                    # for Beam Search
                    is_a_better = child_a.value - child_b.value > contrastive_threshold
                if is_a_better:
                    preference_pairs.append({
                        "instruction": node.trajectory,
                        "reflection": node.reflection,
                        "preferred_response": f"Step {child_a.depth}: {child_a.content}",
                        "dispreferred_response": f"Step {child_b.depth}: {child_b.content}",
                    })

        # Step 2: Recurse into child nodes
        for child in node.children:
            traverse_tree(child)

    # Start traversal from the root
    traverse_tree(root)

    return preference_pairs


class Reasoner:
    def __init__(self, llm_config: dict[str, Any], reason_config: Optional[dict[str, Any]] = None):
        """Initialize a ReasoningAgent that uses tree-of-thought reasoning.

        Args:
            llm_config (dict): Configuration for the language model
            reason_config (Optional[dict[str, Any]]): Configuration for the reasoning method.
                method (str): The search strategy to use. Options:
                    - "beam_search" (default): Uses beam search with parallel paths
                    - "mcts": Uses Monte Carlo Tree Search for exploration
                    - "lats": Uses Language Agent Tree Search with per-step rewards
                    - "dfs": Uses depth-first search (equivalent to beam_search with beam_size=1)

                Common parameters:
                    max_depth (int): Maximum depth of reasoning tree (default: 3)
                    forest_size (int): Number of independent trees to maintain (default: 1)
                    rating_scale (int): Scale for grading responses, e.g. 1-10 (default: 10)

                Beam Search specific:
                    beam_size (int): Number of parallel paths to maintain (default: 3)
                    answer_approach (str): How to select final answer, "pool" or "best" (default: "pool")

                MCTS/LATS specific:
                    nsim (int): Number of simulations to run (default: 3)
                    exploration_constant (float): UCT exploration parameter (default: 1.41)

                Example configs:
                    `{"method": "beam_search", "beam_size": 5, "max_depth": 4}`
                    `{"method": "mcts", "nsim": 10, "exploration_constant": 2.0}`
                    `{"method": "lats", "nsim": 5, "forest_size": 3}`
        """
        reason_config = reason_config or {}

        if isinstance(llm_config, str):
            llm_config = {'default': llm_config}
        self._llm_config: dict[str, Any] = llm_config
        self._reason_config: dict[str, Any] = reason_config or {}
        self._method: Literal["beam_search", "mcts", "lats", "dfs"] = reason_config.get("method", "beam_search")  # noqa
        if self._method not in ["beam_search", "mcts", "lats", "dfs"]:
            raise ValueError(
                f"Invalid reasoning method specified: '{self._method}'. Should be one of 'beam_search', 'mcts', 'lats', or 'dfs'."
            )

        self._beam_size: int = 1
        if self._method in ["beam_search", "dfs"]:
            if self._method != "dfs":
                self._beam_size = reason_config.get("beam_size", 3)
            self._answer_approach: Literal["pool", "best"] = reason_config.get("answer_approach", "pool")  # noqa
            if self._answer_approach not in ["pool", "best"]:
                raise ValueError(
                    f"Invalid answer_approach specified: '{self._answer_approach}'. Should be one of 'pool' or 'best'."
                )
        elif self._method in ["mcts", "lats"]:
            self._nsim: int = reason_config.get("nsim", 3)
            self._exploration_constant: float = reason_config.get("exploration_constant", 1.41)

        self._max_depth: int = reason_config.get("max_depth", 4)
        self._forest_size: int = reason_config.get("forest_size", 1)
        self._rating_scale: int = reason_config.get("rating_scale", 10)

        self._root: Optional[ThinkNode] = None
        self._lats_context: str = ""
        self._get_agents()

    def _get_agents(self):
        self._default_agent = Agent(name="default", instructions=default_system, model=self._get_llm_model('default'))
        self._thinker = Agent(name="tot_thinker", instructions=TREEOFTHOUGHT_MESSAGE,
                              model=self._get_llm_model('thinker'))
        self._grader = Agent(name="tot_grader", model=self._get_llm_model('grader'))
        self._prompt_rewriter = Agent(name="prompt_rewriter", model=self._get_llm_model('rewriter'))

    def _get_llm_model(self, type_name: str):
        return get_chat_model(self._llm_config.get(type_name) or self._llm_config.get("default"))

    async def run(self, prompt: str, ground_truth: str | None = None) -> str:
        """Generate a response using tree-of-thought reasoning.

        Args:
            prompt (str): prompt
            ground_truth (str): ground truth

        Returns:
            generated response
        """
        forest_answers: list[str] = []
        for _ in range(self._forest_size):
            with trace(self._method):
                if self._method in ["beam_search", "dfs"]:
                    response = await self._beam_reply(prompt, ground_truth)
                elif self._method in ["mcts", "lats"]:
                    response = await self._mtcs_reply(prompt, ground_truth)
                else:
                    raise ValueError("Invalid reasoning method specified.")

                forest_answers.append(response)

        if len(forest_answers) == 1:
            return forest_answers[0]
        else:
            forest_answers_str = "-" + "\n-".join(forest_answers)
            result = await self._get_final_answer(
                f"Answer the question {prompt}. Here are some students' different answers:\n{forest_answers_str}")
            return result

    async def rate_node(self, node: ThinkNode, ground_truth: Optional[str] = None, is_outcome: bool = False) -> float:
        """Rate the quality of a reasoning path or the final answer using the grader agent.

        Args:
            node (ThinkNode): Node containing the reasoning trajectory to evaluate
            ground_truth (Optional[str]): Optional ground truth to provide to the grader
            is_outcome (bool): indicates whether the rating is for an outcome (final answer) or a process (thinking trajectory).

        Returns:
            float: Normalized score between 0 and 1 indicating trajectory quality
        """
        if node.value > 0 and node.rating_details:
            # we already calculated the rating for the node
            return node.value

        # Update Grader's system message
        message = ((outcome_rating_prompt if is_outcome else scale_rating_prompt)
                   .replace('{rating_scale}', str(self._rating_scale)))

        # Add ground truth to the message.
        if ground_truth:
            # override the system message
            message += f"--- Note that the Ground Truth is ---\n{ground_truth}\n---\n"
        self._grader.instructions = message

        if self._method == "lats":
            prompt = self._lats_context + "\n\n---\n\n" + f"Rate:\n{node.trajectory}"
        else:
            prompt = f"Rate:\n{node.trajectory}"

        rating = await self._get_final_answer(prompt, agent=self._grader)
        node.rating_details = rating

        try:
            # Scale rating to [0, 1]
            reward = (float(re.findall(r"[\d.]+", rating)[0]) - 1.0) / (self._rating_scale - 1.0)
        except (IndexError, ValueError):
            reward = 0.0  # Default reward if parsing fails
        return reward

    async def _get_final_answer(self, prompt, agent=None):
        reply = await Runner.run(agent or self._default_agent, prompt)
        return reply.final_output

    async def _beam_reply(self, prompt: str, ground_truth: Optional[str] = None) -> str:
        """Generate a response using tree-of-thought reasoning.

        Implements beam search through a tree of reasoning steps, using the thinker
        agent to generate possible next steps and the grader agent to evaluate paths.

        Args:
            prompt (str): The question or prompt to generate a response for.
            ground_truth (Optional[str]): The ground truth or correct answer for evaluation.

        Returns:
            str: The generated response based on the reasoning process.
        """
        root = ThinkNode(content=prompt, parent=None)
        self._root = root  # save the root node for later visualization
        prev_leafs: list[ThinkNode] = [root]
        final_answers: set[ThinkNode] = set()  # store the final answers

        while prev_leafs and len(final_answers) < self._beam_size:
            new_leafs: list[ThinkNode] = []
            for node in prev_leafs:
                if self._is_terminal(node):
                    # Reached max depth; collect possible answers
                    if node.value is None:
                        node.value = await self.rate_node(node, ground_truth)
                    final_answers.add(node)
                    continue

                new_leafs += await self._expand(node)

            prev_leafs = new_leafs

            if len(prev_leafs) + len(final_answers) > self._beam_size:
                if len(final_answers) >= self._beam_size:
                    prev_leafs = []  # stop searching, max beam size reached
                    break

                # Rate
                for node in prev_leafs:
                    node.value = await self.rate_node(node, ground_truth)
                # Beam search: keep top beam_size leaf nodes
                prev_leafs = sorted(prev_leafs, key=lambda x: x.value if x.value else 0, reverse=True)[
                             : self._beam_size - len(final_answers)
                             ]

        assert final_answers, "No final answers found."
        final_answers_list = list(final_answers)

        if self._answer_approach == "best":
            # Best the final answers
            best_leaf = max(final_answers_list, key=lambda x: x.value)
            final_answer = await self._get_final_answer(f"Answer the question {prompt}. " +
                                                        f"Here is my thinking processes:\n{best_leaf.trajectory}")
        elif self._answer_approach == "pool":
            all_thoughts = "\n\n".join([
                f"--- Possibility {i + 1} ---\n{node.trajectory}\n" for i, node in enumerate(final_answers_list)
            ])
            final_answer = await self._get_final_answer(
                f"Answer the question {prompt}." +
                f" You can utilize these possible different thinking processes.\n\n{all_thoughts}")
        else:
            raise NotImplementedError('Unknown answer approach.')

        return final_answer

    @staticmethod
    async def _run_questions(questions: list[Question]) -> list[Runner]:
        return await asyncio.gather(*[Runner.run(question.agent, question.prompt) for question in questions])

    async def _mtcs_reply(self, prompt: str, ground_truth: Optional[str] = None) -> str:
        """Generate a response using Monte Carlo Tree Search (MCTS) reasoning.

        Args:
            prompt (str): The question or prompt to generate a response for.
            ground_truth (Optional[str]): The ground truth or correct answer for evaluation.

        Returns:
            str: The generated response based on the reasoning process.
        """
        root = ThinkNode(content=prompt, parent=None)
        self._root = root
        self._lats_context = "## Here are some previous trajectories and reflections\n\n"  # Store LATS's reflections

        questions: list[Question] = []
        for _ in range(self._nsim):
            node = root

            # Selection
            while not self._is_terminal(node) and len(node.children) > 0:
                choices_weights = [
                    (child.value / (child.visits + EPSILON))
                    + self._exploration_constant
                    * math.sqrt(2 * math.log(node.visits + EPSILON) / (child.visits + EPSILON))
                    for child in node.children
                ]
                node = node.children[choices_weights.index(max(choices_weights))]

            # Expansion and Simulation
            while not self._is_terminal(node):
                if len(node.children) == 0:
                    await self._expand(node)
                if len(node.children) == 0:
                    node.content += "\nTERMINATE"
                    break
                node = random.choice(node.children)

            # Add answer (leaf) node and evaluate answer
            questions.append(Question(node=node,
                                      agent=self._default_agent,
                                      prompt=
                                      f"Answer the question {prompt}. Here is my thinking process:\n{node.trajectory}"))
        replies = await self._run_questions(questions)

        answer_nodes: list[ThinkNode] = []
        best_ans_node = None
        # TODO: parallelize
        for question, reply in zip(questions, replies):
            _answer = reply.final_output
            node = question.node
            _ans_node = ThinkNode(content=_answer, parent=node)
            reward = await self.rate_node(_ans_node, ground_truth, is_outcome=True)
            _ans_node.value = reward
            answer_nodes.append(_ans_node)
            self._lats_context += f"### Previous Tries:\n{node.trajectory}\n\nRating:{_ans_node.rating_details}\n\n"
            node.backpropagate(reward)

            best_ans_node = max(answer_nodes, key=lambda _node: _node.value)
        return best_ans_node.content

    async def _expand(self, node: ThinkNode) -> list[ThinkNode]:
        """Expand the node by generating possible next steps based on the current trajectory.

        This method sends a message to the thinker agent, asking for possible next steps
        that can be taken from the current node's trajectory. It processes the response to
        extract the options provided by the thinker and creates new ThinkNode instances
        for each option.

        Args:
            node (ThinkNode): The node to expand, representing the current state in the reasoning process.

        Returns:
            list[ThinkNode]: A list of new ThinkNode instances created from the options provided by the thinker.
        """

        if self._method == "lats":
            prompt = self._lats_context + "\n\n---\n\n" + f"{node.trajectory}\n---\nWhat are the possible next steps?"
        else:
            prompt = f"{node.trajectory}\n---\nWhat are the possible next steps?"

        reply = await Runner.run(self._thinker, prompt)

        reflection = re.findall(r"REFLECTION:\s*(.+?)(?=\*\*Possible Options:\*\*|Option \d+:|$)",
                                reply.final_output, re.DOTALL)
        if reflection:
            node.reflection += str(reflection[0].strip())
        options = re.findall(r"Option \d+:(.+?)(?=Option \d+:|$)", reply.final_output, re.DOTALL)

        option_nodes = [ThinkNode(content=option.strip().rstrip(), parent=node) for option in options]

        return option_nodes

    def _is_terminal(self, node: ThinkNode) -> bool:
        """Check if the node is a terminal state in the reasoning process.

        Args:
            node (ThinkNode): The node to check for terminal state.

        Returns:
            bool: True if the node is terminal, False otherwise.
        """
        return node.depth >= self._max_depth or "TERMINATE" in node.content

    @property
    def method(self) -> str:
        """Get the reasoning method being used.

        Returns:
            str: The name of the reasoning method
        """
        return self._method

    def visualize_tree(self, filename) -> None:
        """Visualize the tree of thoughts using graphviz.

        Raises:
            RuntimeError: If the tree has not been generated yet.
        """
        if self._root:
            self._root.visualize_tree(filename)
        else:
            raise RuntimeError("No tree to visualize. Run the reasoning process first.")

    def extract_sft_dataset(self) -> list[dict[str, Any]]:
        """Extract the best trajectory or multiple equally good trajectories for SFT training.

        Returns:
            list[dict]: list of best trajectories, each one is a pair of instruction and response.

        Raises:
            RuntimeError: If the tree has not been generated yet.
        """
        if self._root:
            return extract_sft_dataset(self._root)
        else:
            raise RuntimeError("No tree to extract dataset from. Run the reasoning process first.")

    def extract_rlhf_preference_dataset(self, contrastive_threshold: float = 0.2) -> list[dict[str, Any]]:
        """Extract and generate preference pairs for RLHF training by comparing sibling nodes.

        Args:
            contrastive_threshold (float): between (0, 1), a distance measure that we are confident to call
                one is positive and another is negative.

        Returns:
            list[dict]: list of preference pairs, where each pair contains two responses and
            indicates which one is preferred.

        Raises:
            RuntimeError: If the tree has not been generated yet.
        """
        if self._root:
            return extract_rlhf_preference_dataset(self._root, contrastive_threshold)
        else:
            raise RuntimeError("No tree to extract dataset from. Run the reasoning process first.")


def test_run() -> Tuple[Reasoner, str]:
    # Example usage of the Reasoner class
    llm_config = {
        "default": "gemini/gemini-2.0-flash",
        "thinker": "gemini/gemini-2.0-flash",
        "grader": "gemini/gemini-2.0-flash",
        "rewriter": "gemini/gemini-2.0-flash",
    }
    reason_config = {
        "method": "beam_search",
        "beam_size": 3,
        "max_depth": 4,
        "rating_scale": 10,
    }

    reasoner = Reasoner(llm_config=llm_config, reason_config=reason_config)

    prompt = r"""
I know the following (where DM, DH, DML, DHL are functions of z where z>=0)

DM(infty) = \int_0^{infty} DH = \int_0^{infty} DHL = DML(infty) 
DH(0) > DHL(0)
DM(0) = DML(0) = 0
DM >= DML
DH = d(DM)/dz 
DHL = d(DML)/dz
d DH/dz < (DH/DHL)^3 d DHL/dz.
DH and DHL are both positive monotonically decreasing functions for z>0.

Can you show that DM/DML is monotonically decreasing?"""

    response = asyncio.run(reasoner.run(prompt))
    return reasoner, response
