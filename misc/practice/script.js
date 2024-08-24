// Add this function at the beginning of your script, before any other code
function $(id) {
    const element = document.getElementById(id);
    if (!element) {
        throw new Error(`Element with id '${id}' not found`);
    }
    return element;
}

const examples = [
    {
        id: "ex1",
        originalGoal: {
            hypotheses: [],
            goal: "forall (n m : nat), n + m = m + n"
        },
        tactic: "intros",
        resultingGoals: [
            {
                hypotheses: ["n, m : nat"],
                goal: "n + m = m + n"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'intros' tactic moves hypotheses from the goal to the context."
    },
    {
        id: "ex2",
        originalGoal: {
            hypotheses: ["n, m : nat"],
            goal: "n + m = m + n"
        },
        tactic: "revert m",
        resultingGoals: [
            {
                hypotheses: ["n : nat"],
                goal: "forall m : nat, n + m = m + n"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'revert' tactic moves a hypothesis from the context back into the goal."
    },
    {
        id: "ex3",
        originalGoal: {
            hypotheses: [],
            goal: "forall (n m : nat), n + m = m + n"
        },
        tactic: "intros n m",
        resultingGoals: [
            {
                hypotheses: ["n, m : nat"],
                goal: "n + m = m + n"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'intros' tactic moves universally quantified variables from the goal to the context."
    },
    {
        id: "ex3b",
        originalGoal: {
            hypotheses: ["n, m : nat"],
            goal: "n + m = m + n"
        },
        tactic: "apply plus_comm",
        resultingGoals: [],
        difficulty: "beginner",
        explanation: "The 'apply' tactic uses the commutativity of addition to prove the goal."
    },
    {
        id: "ex4",
        originalGoal: {
            hypotheses: [],
            goal: "forall (b : bool), if b then true else false = b"
        },
        tactic: "destruct b",
        resultingGoals: [
            {
                hypotheses: [],
                goal: "if true then true else false = true"
            },
            {
                hypotheses: [],
                goal: "if false then true else false = false"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'destruct' tactic breaks down a hypothesis into its constituent parts, creating separate subgoals for each case."
    },
    {
        id: "ex5",
        originalGoal: {
            hypotheses: ["n m : nat"],
            goal: "n + m = m + n"
        },
        tactic: "rewrite plus_comm",
        resultingGoals: [
            {
                hypotheses: ["n m : nat"],
                goal: "m + n = m + n"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'rewrite' tactic rewrites the goal using the commutativity of addition."
    },
    {
        id: "ex6",
        originalGoal: {
            hypotheses: [],
            goal: "forall (A B : Prop), A /\\ B -> B /\\ A"
        },
        tactic: "intros A B H",
        resultingGoals: [
            {
                hypotheses: ["A, B : Prop", "H : A /\\ B"],
                goal: "B /\\ A"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'intros' tactic moves hypotheses from the goal to the context."
    },
    {
        id: "ex7",
        originalGoal: {
            hypotheses: ["A, B : Prop", "H : A /\\ B"],
            goal: "B /\\ A"
        },
        tactic: "destruct H as [HA HB]",
        resultingGoals: [
            {
                hypotheses: ["A, B : Prop", "HA : A", "HB : B"],
                goal: "B /\\ A"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'destruct' tactic breaks down a hypothesis into its constituent parts."
    },
    {
        id: "ex8",
        originalGoal: {
            hypotheses: [],
            goal: "forall (P Q : nat -> Prop), (forall n, P n -> Q n) -> (forall n, P n) -> (forall n, Q n)"
        },
        tactic: "intros P Q H1 H2 n",
        resultingGoals: [
            {
                hypotheses: ["P, Q : nat -> Prop", "H1 : forall n, P n -> Q n", "H2 : forall n, P n", "n : nat"],
                goal: "Q n"
            }
        ],
        difficulty: "advanced",
        explanation: "The 'intros' tactic moves hypotheses from the goal to the context."
    },
    {
        id: "ex9",
        originalGoal: {
            hypotheses: [],
            goal: "forall (A B C : Prop), (A -> B) -> (B -> C) -> A -> C"
        },
        tactic: "intros A B C HAB HBC HA",
        resultingGoals: [
            {
                hypotheses: ["A, B, C : Prop", "HAB : A -> B", "HBC : B -> C", "HA : A"],
                goal: "C"
            }
        ],
        difficulty: "advanced",
        explanation: "The 'intros' tactic moves hypotheses from the goal to the context."
    },
    {
        id: "ex10",
        originalGoal: {
            hypotheses: ["n : nat"],
            goal: "n = n"
        },
        tactic: "reflexivity",
        resultingGoals: [],
        difficulty: "beginner",
        explanation: "The 'reflexivity' tactic proves a goal of the form 'x = x' for any term x."
    },
    {
        id: "ex11",
        originalGoal: {
            hypotheses: [],
            goal: "forall (n : nat), n <= n"
        },
        tactic: "intros n",
        resultingGoals: [
            {
                hypotheses: ["n : nat"],
                goal: "n <= n"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'intros' tactic moves the universally quantified variable from the goal to the context."
    },
    {
        id: "ex12",
        originalGoal: {
            hypotheses: ["n : nat"],
            goal: "n <= n"
        },
        tactic: "apply le_n",
        resultingGoals: [],
        difficulty: "beginner",
        explanation: "The 'apply' tactic uses the lemma 'le_n' to prove that any natural number is less than or equal to itself.",
        context: "Lemma le_n : forall n : nat, n <= n"
    },
    {
        id: "ex13",
        originalGoal: {
            hypotheses: ["n : nat"],
            goal: "S n <> 0"
        },
        tactic: "discriminate",
        resultingGoals: [],
        difficulty: "beginner",
        explanation: "The 'discriminate' tactic proves that two constructors of an inductive type are not equal."
    },
    {
        id: "ex14",
        originalGoal: {
            hypotheses: ["n : nat", "H : S n = 0"],
            goal: "False"
        },
        tactic: "inversion H",
        resultingGoals: [],
        difficulty: "intermediate",
        explanation: "The 'inversion' tactic derives contradictions from impossible equalities between constructors."
    },
    {
        id: "ex15",
        originalGoal: {
            hypotheses: ["n : nat"],
            goal: "n + 0 = n"
        },
        tactic: "induction n",
        resultingGoals: [
            {
                hypotheses: [],
                goal: "0 + 0 = 0"
            },
            {
                hypotheses: ["n : nat", "IHn : n + 0 = n"],
                goal: "S n + 0 = S n"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'induction' tactic starts a proof by induction on a given variable, generating base and inductive cases."
    },
    {
        id: "ex16",
        originalGoal: {
            hypotheses: ["A B : Prop", "H : A /\\ B"],
            goal: "A"
        },
        tactic: "destruct H",
        resultingGoals: [
            {
                hypotheses: ["A B : Prop", "H1 : A", "H2 : B"],
                goal: "A"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'destruct' tactic breaks down a conjunction into its components."
    },
    {
        id: "ex17",
        originalGoal: {
            hypotheses: ["A B : Prop"],
            goal: "A \\/ B -> B \\/ A"
        },
        tactic: "intros H",
        resultingGoals: [
            {
                hypotheses: ["A B : Prop", "H : A \\/ B"],
                goal: "B \\/ A"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'intros' tactic moves a hypothesis from the goal to the context."
    },
    {
        id: "ex18",
        originalGoal: {
            hypotheses: ["A B : Prop", "H : A \\/ B"],
            goal: "B \\/ A"
        },
        tactic: "destruct H",
        resultingGoals: [
            {
                hypotheses: ["A B : Prop", "H : A"],
                goal: "B \\/ A"
            },
            {
                hypotheses: ["A B : Prop", "H : B"],
                goal: "B \\/ A"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'destruct' tactic breaks down a disjunction into separate cases."
    },
    {
        id: "ex19",
        originalGoal: {
            hypotheses: ["P Q : Prop", "H : P <-> Q"],
            goal: "Q -> P"
        },
        tactic: "destruct H",
        resultingGoals: [
            {
                hypotheses: ["P Q : Prop", "H1 : P -> Q", "H2 : Q -> P"],
                goal: "Q -> P"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'destruct' tactic breaks down a bi-implication into its two implications."
    },
    {
        id: "ex20",
        originalGoal: {
            hypotheses: ["n : nat"],
            goal: "exists m : nat, n = m"
        },
        tactic: "exists n",
        resultingGoals: [
            {
                hypotheses: ["n : nat"],
                goal: "n = n"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'exists' tactic provides a witness for an existential statement."
    },
    {
        id: "ex21",
        originalGoal: {
            hypotheses: [],
            goal: "forall (A B C : Prop), A -> B -> C -> A /\\ B /\\ C"
        },
        tactic: "intros A B C HA HB HC",
        resultingGoals: [
            {
                hypotheses: ["A B C : Prop", "HA : A", "HB : B", "HC : C"],
                goal: "A /\\ B /\\ C"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'intros' tactic moves multiple hypotheses from the goal to the context."
    },
    {
        id: "ex22",
        originalGoal: {
            hypotheses: ["A B : Prop", "H : A /\\ B"],
            goal: "B /\\ A"
        },
        tactic: "destruct H as [HA HB]",
        resultingGoals: [
            {
                hypotheses: ["A B : Prop", "HA : A", "HB : B"],
                goal: "B /\\ A"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'destruct' tactic breaks down a conjunction hypothesis into its components."
    },
    {
        id: "ex23",
        originalGoal: {
            hypotheses: ["A B : Prop", "HA : A", "HB : B"],
            goal: "A /\\ B"
        },
        tactic: "split",
        resultingGoals: [
            {
                hypotheses: ["A B : Prop", "HA : A", "HB : B"],
                goal: "A"
            },
            {
                hypotheses: ["A B : Prop", "HA : A", "HB : B"],
                goal: "B"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'split' tactic breaks down a conjunction goal into separate subgoals."
    },
    {
        id: "ex24",
        originalGoal: {
            hypotheses: ["A B : Prop", "HA : A"],
            goal: "A \\/ B"
        },
        tactic: "left",
        resultingGoals: [
            {
                hypotheses: ["A B : Prop", "HA : A"],
                goal: "A"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'left' tactic chooses the left side of a disjunction goal."
    },
    {
        id: "ex25",
        originalGoal: {
            hypotheses: ["A B : Prop", "HB : B"],
            goal: "A \\/ B"
        },
        tactic: "right",
        resultingGoals: [
            {
                hypotheses: ["A B : Prop", "HB : B"],
                goal: "B"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'right' tactic chooses the right side of a disjunction goal."
    },
    {
        id: "ex26",
        originalGoal: {
            hypotheses: ["n : nat"],
            goal: "n + 0 = n"
        },
        tactic: "induction n",
        resultingGoals: [
            {
                hypotheses: [],
                goal: "0 + 0 = 0"
            },
            {
                hypotheses: ["n : nat", "IHn : n + 0 = n"],
                goal: "S n + 0 = S n"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'induction' tactic starts a proof by induction on a natural number."
    },
    {
        id: "ex27",
        originalGoal: {
            hypotheses: ["n m : nat"],
            goal: "S (n + m) = S n + m"
        },
        tactic: "reflexivity",
        resultingGoals: [],
        difficulty: "beginner",
        explanation: "The 'reflexivity' tactic proves the goal because both sides are already equal by definition of addition."
    },
    {
        id: "ex28",
        originalGoal: {
            hypotheses: ["n m : nat", "H : n = m"],
            goal: "S n = S m"
        },
        tactic: "rewrite H",
        resultingGoals: [
            {
                hypotheses: ["n m : nat", "H : n = m"],
                goal: "S m = S m"
            }
        ],
        difficulty: "beginner",
        explanation: "The 'rewrite' tactic replaces occurrences of the left-hand side of an equality with its right-hand side."
    },
    {
        id: "ex29",
        originalGoal: {
            hypotheses: ["n : nat"],
            goal: "S n <> 0"
        },
        tactic: "discriminate",
        resultingGoals: [],
        difficulty: "beginner",
        explanation: "The 'discriminate' tactic proves that two constructors of an inductive type are not equal."
    },
    {
        id: "ex30",
        originalGoal: {
            hypotheses: ["n m : nat", "H : S n = S m"],
            goal: "n = m"
        },
        tactic: "injection H",
        resultingGoals: [
            {
                hypotheses: ["n m : nat", "H : S n = S m", "H0 : n = m"],
                goal: "n = m"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'injection' tactic derives an equality of arguments from an equality of constructed terms, adding it as a new hypothesis."
    },
    {
        id: "ex31",
        originalGoal: {
            hypotheses: ["n m : nat", "H1 : S n = m", "H2 : m = S n"],
            goal: "n = n"
        },
        tactic: "congruence",
        resultingGoals: [],
        difficulty: "intermediate",
        explanation: "The 'congruence' tactic proves goals involving equalities and inequalities using congruence closure."
    },
    {
        id: "ex32",
        originalGoal: {
            hypotheses: ["n m : nat", "H1 : n <= m", "H2 : m <= n"],
            goal: "n = m"
        },
        tactic: "lia",
        resultingGoals: [],
        difficulty: "intermediate",
        explanation: "The 'lia' tactic solves goals involving linear integer arithmetic."
    },
    {
        id: "ex33",
        originalGoal: {
            hypotheses: ["n : nat"],
            goal: "even n \\/ odd n"
        },
        tactic: "induction n",
        resultingGoals: [
            {
                hypotheses: [],
                goal: "even 0 \\/ odd 0"
            },
            {
                hypotheses: ["n : nat", "IHn : even n \\/ odd n"],
                goal: "even (S n) \\/ odd (S n)"
            }
        ],
        difficulty: "advanced",
        explanation: "The 'induction' tactic can be used on inductive propositions like 'even' and 'odd'.",
        context: "Inductive even : nat -> Prop :=\n  | even_O : even 0\n  | even_SS : forall n, even n -> even (S (S n)).\n\nInductive odd : nat -> Prop :=\n  | odd_S : odd 1\n  | odd_SS : forall n, odd n -> odd (S (S n))."
    },
    {
        id: "ex34",
        originalGoal: {
            hypotheses: ["n : nat", "H : even (S n)"],
            goal: "odd n"
        },
        tactic: "inversion H",
        resultingGoals: [
            {
                hypotheses: ["n : nat", "H : even (S n)", "n0 : nat", "H0 : n = S n0", "H1 : odd n0"],
                goal: "odd n"
            }
        ],
        difficulty: "advanced",
        explanation: "The 'inversion' tactic analyzes the structure of an inductive hypothesis, generating all possible cases."
    },
    {
        id: "ex35",
        originalGoal: {
            hypotheses: ["f g : nat -> nat", "H : forall x, f x = g x"],
            goal: "f 3 = g 3"
        },
        tactic: "apply H",
        resultingGoals: [],
        difficulty: "intermediate",
        explanation: "The 'apply' tactic uses a hypothesis to prove the goal, instantiating universal quantifiers as needed."
    },
    {
        id: "ex36",
        originalGoal: {
            hypotheses: ["H1 : A -> B", "H2 : B -> C", "H3 : A"],
            goal: "C"
        },
        tactic: "auto",
        resultingGoals: [],
        difficulty: "beginner",
        explanation: "The 'auto' tactic attempts to solve the goal automatically using the available hypotheses and simple proof strategies."
    },
    {
        id: "ex37",
        originalGoal: {
            hypotheses: ["n : nat"],
            goal: "double n = n + n"
        },
        tactic: "unfold double",
        resultingGoals: [
            {
                hypotheses: ["n : nat"],
                goal: "2 * n = n + n"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'unfold' tactic expands the definition of a function or constant in the goal.",
        context: "Definition double (n : nat) := 2 * n."
    },
    {
        id: "ex38",
        originalGoal: {
            hypotheses: ["n : nat"],
            goal: "n + 1 > n"
        },
        tactic: "assert (H: n + 1 = S n)",
        resultingGoals: [
            {
                hypotheses: ["n : nat"],
                goal: "n + 1 = S n"
            },
            {
                hypotheses: ["n : nat", "H : n + 1 = S n"],
                goal: "n + 1 > n"
            }
        ],
        difficulty: "intermediate",
        explanation: "The 'assert' tactic introduces a new subgoal and adds it as a hypothesis once proved, which can be useful for breaking down complex proofs."
    }
];

let currentExampleIndex = 0;
let quizMode = false;
let currentDifficulty = "all";
let progress = JSON.parse(localStorage.getItem('coqTacticProgress')) || {
    completedExamples: {}
};

function displayExample(index) {
    const example = examples[index];
    
    $('original-goal').innerHTML = createGoalHTML(example.originalGoal);
    
    const tacticElement = $('tactic');
    const quizInput = $('quiz-input');
    const quizFeedback = $('quiz-feedback');
    if (quizMode) {
        tacticElement.style.display = 'none';
        quizInput.style.display = 'block';
        quizFeedback.style.display = 'block';
        quizInput.value = '';
        quizFeedback.textContent = '';
        quizInput.focus();
        quizInput.classList.remove('correct', 'incorrect');
    } else {
        tacticElement.style.display = 'flex';
        quizInput.style.display = 'none';
        quizFeedback.style.display = 'none';
        tacticElement.innerHTML = `<span>${example.tactic}</span>`;
    }
    
    const resultingGoalsContainer = $('resulting-goals');
    resultingGoalsContainer.innerHTML = example.resultingGoals.length === 0 
        ? '<div class="goal"><div class="goal-content">Proof completed</div></div>'
        : example.resultingGoals.map(createGoalHTML).join('');
    
    const explanationElement = $('explanation');
    explanationElement.textContent = example.explanation;
    explanationElement.style.display = quizMode ? 'none' : 'block';

    // Display context if present, after the explanation
    const contextElement = $('context');
    if (example.context) {
        contextElement.innerHTML = Prism.highlight(example.context, Prism.languages.coq, 'coq');
        contextElement.style.display = 'block';
    } else {
        contextElement.style.display = 'none';
    }

    // Add completion indicator
    const appContainer = $('app');
    if (progress.completedExamples[example.id]) {
        appContainer.classList.add('completed');
    } else {
        appContainer.classList.remove('completed');
    }

    updateProgress();
}

function updateProgress() {
    const progressBar = $('progress-bar');
    const progressElement = $('progress');
    progressBar.style.display = 'block';

    const relevantExamples = examples.filter(ex => currentDifficulty === "all" || ex.difficulty === currentDifficulty);
    const totalExamples = relevantExamples.length;

    if (quizMode) {
        const completedExamples = relevantExamples.filter(ex => progress.completedExamples[ex.id]).length;
        const progressPercentage = (completedExamples / totalExamples) * 100;
        progressElement.style.width = `${progressPercentage}%`;
        progressElement.classList.add('quiz-mode');
        progressElement.classList.remove('progress-mode');
    } else {
        // Find the index of the current example within the relevant examples
        const currentExampleIndexInRelevant = relevantExamples.findIndex(ex => ex.id === examples[currentExampleIndex].id);
        const progressPercentage = ((currentExampleIndexInRelevant + 1) / totalExamples) * 100;
        progressElement.style.width = `${progressPercentage}%`;
        progressElement.classList.add('progress-mode');
        progressElement.classList.remove('quiz-mode');
    }
    
    // Update difficulty select options
    const difficultySelect = $('difficulty');
    for (let i = 0; i < difficultySelect.options.length; i++) {
        const option = difficultySelect.options[i];
        const difficulty = option.value;
        if (difficulty !== 'all' && difficulty !== 'reset') {
            const difficultyTotal = examples.filter(ex => ex.difficulty === difficulty).length;
            const difficultyProgress = examples.filter(ex => 
                ex.difficulty === difficulty && progress.completedExamples[ex.id]
            ).length;
            const percentage = Math.round((difficultyProgress / difficultyTotal) * 100);
            option.textContent = `${difficulty.charAt(0).toUpperCase() + difficulty.slice(1)} (${percentage}%)`;
        }
    }

    localStorage.setItem('coqTacticProgress', JSON.stringify(progress));
}

function createGoalHTML(goalObject) {
    return `
        <div class="goal">
            <div class="goal-content">${Prism.highlight(goalObject.hypotheses.join('\n'), Prism.languages.coq, 'coq')}</div>
            <div class="horizontal-bar"></div>
            <div class="goal-content">${Prism.highlight(goalObject.goal, Prism.languages.coq, 'coq')}</div>
        </div>
    `;
}

function nextExample() {
    do {
        currentExampleIndex = (currentExampleIndex + 1) % examples.length;
    } while (currentDifficulty !== "all" && examples[currentExampleIndex].difficulty !== currentDifficulty);
    displayExample(currentExampleIndex);
    updateProgress();
}

function prevExample() {
    do {
        currentExampleIndex = (currentExampleIndex - 1 + examples.length) % examples.length;
    } while (currentDifficulty !== "all" && examples[currentExampleIndex].difficulty !== currentDifficulty);
    displayExample(currentExampleIndex);
    updateProgress();
}

function resetProgress() {
    progress = {
        completedExamples: {}
    };
    localStorage.setItem('coqTacticProgress', JSON.stringify(progress));
    currentExampleIndex = 0; // Reset to the first example
    displayExample(currentExampleIndex);
    updateProgress();
}

// Add these variables at the beginning of the file, after the existing variables
let touchStartX = 0;
let touchEndX = 0;

// Add this function to handle touch events
function handleTouchEvents() {
    const app = $('app');

    app.addEventListener('touchstart', (e) => {
        touchStartX = e.changedTouches[0].screenX;
    }, { passive: true });

    app.addEventListener('touchend', (e) => {
        touchEndX = e.changedTouches[0].screenX;
        handleSwipe();
    }, { passive: true });
}

// Add this function to determine the swipe direction and navigate accordingly
function handleSwipe() {
    const swipeThreshold = 50; // Minimum distance (in pixels) to trigger a swipe
    const swipeDistance = touchEndX - touchStartX;

    if (swipeDistance > swipeThreshold) {
        prevExample(); // Swipe right
    } else if (swipeDistance < -swipeThreshold) {
        nextExample(); // Swipe left
    }
}

// Modify the existing event listeners section to include touch events
document.addEventListener('DOMContentLoaded', () => {
    $('next-example').addEventListener('click', nextExample);
    $('prev-example').addEventListener('click', prevExample);

    $('difficulty').addEventListener('change', (e) => {
        if (e.target.value === 'reset') {
            if (confirm('Are you sure you want to reset all progress?')) {
                resetProgress();
            }
            e.target.value = currentDifficulty; // Reset the select to the previous value
        } else {
            currentDifficulty = e.target.value;
            currentExampleIndex = -1;
            nextExample();
        }
    });

    $('toggle-quiz-mode').addEventListener('click', () => {
        quizMode = !quizMode;
        $('toggle-quiz-mode').classList.toggle('quiz-mode');
        displayExample(currentExampleIndex);
        $('quiz-feedback').textContent = '';
        $('quiz-input').classList.remove('correct', 'incorrect');
        // If quiz mode is turned on, trigger the quiz-input input event
        $('quiz-input').dispatchEvent(new Event('input'));
    });

    $('quiz-input').addEventListener('input', (e) => {
        if (!quizMode) return;

        const userAnswer = e.target.value.trim().toLowerCase();
        const correctAnswer = examples[currentExampleIndex].tactic.toLowerCase();
        const quizInput = $('quiz-input');
        const quizFeedback = $('quiz-feedback');
        
        if (userAnswer === "") {
            quizFeedback.textContent = "Enter the tactic.";
            quizFeedback.style.color = "black";
            quizInput.classList.remove('correct', 'incorrect');
        } else if (userAnswer === correctAnswer) {
            quizFeedback.textContent = "Correct!";
            quizFeedback.style.color = "green";
            quizInput.classList.add('correct');
            quizInput.classList.remove('incorrect');
            progress.completedExamples[examples[currentExampleIndex].id] = true;
            updateProgress();
            setTimeout(() => {
                nextExample();
                quizInput.value = ''; // Clear the input field
                quizInput.classList.remove('correct', 'incorrect');
                quizFeedback.textContent = '';
            }, 1000); // 1 second delay before moving to the next question
        } else if (correctAnswer.startsWith(userAnswer)) {
            quizFeedback.textContent = "Keep going...";
            quizFeedback.style.color = "blue";
            quizInput.classList.remove('correct', 'incorrect');
        } else {
            quizFeedback.textContent = "Incorrect. Try again!";
            quizFeedback.style.color = "red";
            quizInput.classList.add('incorrect');
            quizInput.classList.remove('correct');
        }
    });

    document.addEventListener('keydown', (e) => {
        if (e.key === 'ArrowRight') nextExample();
        if (e.key === 'ArrowLeft') prevExample();
    });

    // Add touch event handling
    handleTouchEvents();

    displayExample(currentExampleIndex);
    updateProgress();
});

$('quiz-input').addEventListener('input', (e) => {
    if (!quizMode) return;

    const userAnswer = e.target.value.trim().toLowerCase();
    const correctAnswer = examples[currentExampleIndex].tactic.toLowerCase();
    const quizInput = $('quiz-input');
    const quizFeedback = $('quiz-feedback');
    
    if (userAnswer === "") {
        quizFeedback.textContent = "Enter the tactic.";
        quizFeedback.style.color = "black";
        quizInput.classList.remove('correct', 'incorrect');
    } else if (userAnswer === correctAnswer) {
        quizFeedback.textContent = "Correct!";
        quizFeedback.style.color = "green";
        quizInput.classList.add('correct');
        quizInput.classList.remove('incorrect');
        progress.completedExamples[examples[currentExampleIndex].id] = true;
        updateProgress();
        setTimeout(() => {
            nextExample();
            quizInput.value = ''; // Clear the input field
            quizInput.classList.remove('correct', 'incorrect');
            quizFeedback.textContent = '';
        }, 1000); // 1 second delay before moving to the next question
    } else if (correctAnswer.startsWith(userAnswer)) {
        quizFeedback.textContent = "Keep going...";
        quizFeedback.style.color = "blue";
        quizInput.classList.remove('correct', 'incorrect');
    } else {
        quizFeedback.textContent = "Incorrect. Try again!";
        quizFeedback.style.color = "red";
        quizInput.classList.add('incorrect');
        quizInput.classList.remove('correct');
    }
});

document.addEventListener('keydown', (e) => {
    if (e.key === 'ArrowRight') nextExample();
    if (e.key === 'ArrowLeft') prevExample();
});

displayExample(currentExampleIndex);
updateProgress();