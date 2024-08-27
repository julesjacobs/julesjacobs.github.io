const $ = (id) => {
    const element = document.getElementById(id);
    if (!element) {
        throw new Error(`Element with id '${id}' not found`);
    }
    return element;
};

const progress = JSON.parse(localStorage.getItem('coqTacticProgress')) || {
    completedExamples: {}
};
let currentExampleIndex = 0;
let quizMode = false;
let currentDifficulty = "all";
let touchStartX = 0;
let touchEndX = 0;

let exampleIdCounter = 0;
const examples = [];

function addExample(tactic, originalGoal, resultingGoals, explanation, context = null) {
    const id = generateId(tactic, explanation);
    const example = {
        id,
        tactic,
        originalGoal: {
            hypotheses: originalGoal.slice(0, -1),
            goal: originalGoal[originalGoal.length - 1]
        },
        resultingGoals: resultingGoals.map(goal => ({
            hypotheses: goal.slice(0, -1),
            goal: goal[goal.length - 1]
        })),
        difficulty: currentDifficulty,
        explanation,
        context
    };
    examples.push(example);
}

function generateId(tactic, explanation) {
    const hash = stringToHash(tactic + explanation);
    return `ex${hash}`;
}

function stringToHash(str) {
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
        const char = str.charCodeAt(i);
        hash = ((hash << 5) - hash) + char;
        hash = hash & hash; // Convert to 32-bit integer
    }
    return Math.abs(hash);
}

currentDifficulty = "connectives";

addExample(
    "intros x",
    ["forall n : nat, n + 0 = n"],
    [["x : nat", "x + 0 = x"]],
    "Introduces a variable x for the first forall quantifier."
);

addExample(
    "intros n m",
    ["forall n m : nat, n + m = m + n"],
    [["n, m : nat", "n + m = m + n"]],
    "Introduces variables n and m for the first two forall quantifiers."
);

addExample(
    "intros H",
    ["n : nat", "n < 2 -> n < 3"],
    [["n : nat", "H : n < 2", "n < 3"]],
    "Introduces a hypothesis H for an implication."
);

addExample(
    "revert m",
    ["n, m : nat", "n + m = m + n"],
    [["n : nat", "forall m : nat, n + m = m + n"]],
    "Moves variable m from the context back into the goal."
);

addExample(
    "revert n m",
    ["n, m : nat", "n + m = m + n"],
    [["forall n m : nat, n + m = m + n"]],
    "Moves variables n and m from the context back into the goal."
);

addExample(
    "constructor",
    ["True"],
    [],
    "Proves a goal of type True by applying its constructor.",
    "Inductive True : Prop := I : True."
);

addExample(
    "destruct H",
    ["H : False", "P"],
    [],
    "Eliminates a hypothesis of type False, proving any goal P.",
    "Inductive False : Prop := ."
);

addExample(
    "apply plus_comm",
    ["n, m : nat", "n + m = m + n"],
    [],
    "Applies the lemma to prove the goal.",
    "Lemma plus_comm : forall n m : nat, n + m = m + n."
);

addExample(
    "apply H",
    ["H : forall n : nat, n + 0 = n", "m : nat", "m + 0 = m"],
    [],
    "Applies the hypothesis H to prove the goal."
);

addExample(
    "apply H in H'",
    ["H : forall n : nat, n < 2 -> n < 3", "m : nat", "H' : m < 2", "m < 3"],
    [["H : forall n : nat, n < 2 -> n < 3", "m : nat", "H' : m < 3", "m < 3"]],
    "Applies the hypothesis H to the hypothesis H'."
);

addExample(
    "apply (H 3)",
    ["H : forall a, n <= a -> a <= m -> n <= m", "n, m : nat", "H1 : n <= 3", "H2 : 3 <= m", "n <= m"],
    [
        ["H : forall a, n <= a -> a <= m -> n <= m", "n, m : nat", "H1 : n <= 3", "H2 : 3 <= m", "n <= 3"],
        ["H : forall a, n <= a -> a <= m -> n <= m", "n, m : nat", "H1 : n <= 3", "H2 : 3 <= m", "3 <= m"],
    ],
    "Instantiate a hypothesis and apply it."
)

addExample(
    "split",
    ["P /\\ Q"],
    [["P"], ["Q"]],
    "Splits a conjunctive goal into two subgoals."
);

addExample(
    "destruct H",
    ["H : P /\\ Q", "Q"],
    [["H1 : P", "H2 : Q", "Q"]],
    "Destructs a conjunctive hypothesis into its components."
);

addExample(
    "destruct H",
    ["H : P \\/ Q", "R"],
    [["H : P", "R"], ["H : Q", "R"]],
    "Performs case analysis on a disjunctive hypothesis."
);

addExample(
    "left",
    ["P \\/ Q"],
    [["P"]],
    "Proves a disjunctive goal by proving its left component."
);

addExample(
    "right",
    ["P \\/ Q"],
    [["Q"]],
    "Proves a disjunctive goal by proving its right component."
);

addExample(
    "exists 2",
    ["exists n, n + 2 = 4"],
    [["2 + 2 = 4"]],
    "Instantiates an existential quantifier with a specific value."
);

addExample(
    "destruct H",
    ["a, b : nat", "H : exists n, a + n = b", "a <= b"], 
    [["a, b, n: nat", "H : a + n = b", "a <= b"]],
    "Destructs an existential hypothesis into its components."
);

currentDifficulty = "data types";

addExample(
    "induction n",
    ["n : nat", "n + 0 = n"],
    [
        ["0 + 0 = 0"],
        ["n : nat", "IHn : n + 0 = n", "(S n) + 0 = S n"]
    ],
    "Performs induction on the natural number n, generating base and inductive cases."
);

addExample(
    "destruct n",
    ["n : nat", "n = 0 \\/ exists m : nat, n = S m"],
    [
        ["0 = 0 \\/ exists m : nat, 0 = S m"],
        ["n' : nat", "S n' = 0 \\/ exists m : nat, S n' = S m"]
    ],
    "Performs case analysis on the natural number n, considering cases for 0 and S n'."
);

addExample(
    "discriminate",
    ["n : nat", "H : S n = 0", "P"],
    [],
    "Proves any goal P by contradiction from an equality between distinct constructors."
);

addExample(
    "injection H as H",
    ["n, m : nat", "H : S n = S m", "n = m"],
    [["n, m : nat", "H : n = m", "n = m"]],
    "Derives an equality between the arguments of matching constructors."
);

currentDifficulty = "equality";

addExample(
    "simpl",
    ["n : nat", "2 + n = n + 2"],
    [["n : nat", "S (S n) = n + 2"]],
    "Simplifies the goal by reducing computations and applying definitions."
);

addExample(
    "simpl in H",
    ["n : nat", "H : 2 + n = n + 3", "False"],
    [["n : nat", "H : S (S n) = n + 3", "False"]],
    "Simplifies the hypothesis H by reducing computations and applying definitions."
);

addExample(
    "reflexivity",
    ["n : nat", "n = n"],
    [],
    "Proves a goal of the form x = x for any term x."
);

addExample(
    "rewrite plus_comm",
    ["n, m, a, b: nat", "n + m = a + b"],
    [["n, m, a, b: nat", "m + n = a + b"]],
    "Rewrites the first match in the goal using a lemma.",
    "Lemma plus_comm : forall n m : nat, n + m = m + n."
);

addExample(
    "rewrite (plus_comm a b)",
    ["n, m, a, b: nat", "n + m = a + b"],
    [["n, m, a, b: nat", "n + m = b + a"]],
    "Rewrites the first match in the goal using an instantiated lemma.",
    "Lemma plus_comm : forall n m : nat, n + m = m + n."
);

addExample(
    "rewrite IHn",
    ["n : nat", "IHn : n + 0 = n", "S (n + 0) = S n"],
    [["n : nat", "IHn : n + 0 = n", "S n = S n"]],
    "Rewrites the goal using the hypothesis IHn."
);

addExample(
    "rewrite plus_comm in H",
    ["n, m : nat", "H : n + 0 = m", "n = m"],
    [["n, m : nat", "H : 0 + n = m", "n = m"]],
    "Rewrites in the hypothesis H using a lemma.",
    "Lemma plus_comm : forall n m : nat, n + m = m + n."
);

addExample(
    "rewrite <-add_0_r",
    ["n : nat", "n = n"],
    [["n : nat", "n + 0 = n"]],
    "Rewrites the goal in reverse.",
    "Lemma add_0_r n : n + 0 = n."
);

addExample(
    "rewrite !add_0_r",
    ["n : nat", "(n + 0) + 0 = n"],
    [["n : nat", "n = n"]],
    "Rewrites the goal repeatedly.",
    "Lemma add_0_r n : n + 0 = n."
);

currentDifficulty = "automation";

addExample(
    "lia",
    ["n, m, k : nat", "n + m = 1", "k < 3", "k + n <= 3 \\/ k + m <= 3"],
    [],
    "Uses a linear integer arithmetic solver to solve the goal."
)

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

    const contextElement = $('context');
    if (example.context) {
        contextElement.innerHTML = Prism.highlight(example.context, Prism.languages.coq, 'coq');
        contextElement.style.display = 'block';
    } else {
        contextElement.style.display = 'none';
    }

    const appContainer = $('app');
    let is_completed = progress.completedExamples[example.id] ? true : false;
    appContainer.classList.toggle('completed', is_completed);

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
        const currentExampleIndexInRelevant = relevantExamples.findIndex(ex => ex.id === examples[currentExampleIndex].id);
        const progressPercentage = ((currentExampleIndexInRelevant + 1) / totalExamples) * 100;
        progressElement.style.width = `${progressPercentage}%`;
        progressElement.classList.add('progress-mode');
        progressElement.classList.remove('quiz-mode');
    }
    
    updateDifficultySelectOptions();
    
    localStorage.setItem('coqTacticProgress', JSON.stringify(progress));
}

function updateDifficultySelectOptions() {
    const difficultySelect = $('difficulty');
    Array.from(difficultySelect.options).forEach(option => {
        const difficulty = option.value;
        if (difficulty !== 'all' && difficulty !== 'reset') {
            const difficultyTotal = examples.filter(ex => ex.difficulty === difficulty).length;
            const difficultyProgress = examples.filter(ex => 
                ex.difficulty === difficulty && progress.completedExamples[ex.id]
            ).length;
            const percentage = Math.round((difficultyProgress / difficultyTotal) * 100);
            option.textContent = `${difficulty.charAt(0).toUpperCase() + difficulty.slice(1)} (${percentage}%)`;
        }
    });
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
}

function moveExample(delta) {
    do {
        currentExampleIndex = (currentExampleIndex + delta + examples.length) % examples.length;
    } while (currentDifficulty !== "all" && examples[currentExampleIndex].difficulty !== currentDifficulty);
    displayExample(currentExampleIndex);
}

function prevExample() {
    moveExample(-1);
}

function resetProgress() {
    progress.completedExamples = {};
    localStorage.removeItem('coqTacticProgress');
    updateProgress();
    displayExample(currentExampleIndex);
}

function handleTouchEvents() {
    const app = document.querySelector('html');

    app.addEventListener('touchstart', (e) => {
        touchStartX = e.changedTouches[0].screenX;
    }, { passive: true });

    app.addEventListener('touchend', (e) => {
        touchEndX = e.changedTouches[0].screenX;
        handleSwipe();
    }, { passive: true });
}

function handleSwipe() {
    const swipeThreshold = 25;
    const swipeDistance = touchEndX - touchStartX;

    if (Math.abs(swipeDistance) > swipeThreshold) {
        swipeDistance > 0 ? prevExample() : nextExample();
    }
}

function handleQuizInput(e) {
    if (!quizMode) return;

    const userAnswer = e.target.value.trim().toLowerCase();
    const correctAnswer = examples[currentExampleIndex].tactic.toLowerCase();
    const quizInput = $('quiz-input');
    const quizFeedback = $('quiz-feedback');
    
    if (userAnswer === "") {
        updateQuizFeedback("Enter the tactic.", "black", quizInput);
    } else if (userAnswer === correctAnswer) {
        handleCorrectAnswer(quizInput, quizFeedback);
    } else if (correctAnswer.startsWith(userAnswer)) {
        updateQuizFeedback("Keep going...", "blue", quizInput);
    } else {
        updateQuizFeedback("Incorrect. Try again!", "red", quizInput, 'incorrect');
    }
}

function updateQuizFeedback(message, color, inputElement, className = '') {
    const quizFeedback = $('quiz-feedback');
    quizFeedback.textContent = message;
    quizFeedback.style.color = color;
    inputElement.classList.remove('correct', 'incorrect');
    if (className) inputElement.classList.add(className);
}

function handleCorrectAnswer(quizInput, quizFeedback) {
    updateQuizFeedback("Correct!", "green", quizInput, 'correct');
    progress.completedExamples[examples[currentExampleIndex].id] = true;
    updateProgress();
    setTimeout(() => {
        nextExample();
        quizInput.value = '';
        quizInput.classList.remove('correct', 'incorrect');
        quizFeedback.textContent = '';
    }, 1000);
}

document.addEventListener('DOMContentLoaded', () => {
    $('next-example').addEventListener('click', nextExample);
    $('prev-example').addEventListener('click', prevExample);

    $('difficulty').addEventListener('change', handleDifficultyChange);

    $('toggle-quiz-mode').addEventListener('click', toggleQuizMode);

    $('quiz-input').addEventListener('input', handleQuizInput);

    document.addEventListener('keydown', handleKeyDown);

    handleTouchEvents();

    displayExample(currentExampleIndex);
    updateProgress();
});

function handleDifficultyChange(e) {
    if (e.target.value === 'reset') {
        if (confirm('Are you sure you want to reset all progress?')) {
            resetProgress();
        }
        e.target.value = currentDifficulty;
    } else {
        currentDifficulty = e.target.value;
        currentExampleIndex = -1;
        nextExample();
    }
}

function toggleQuizMode() {
    quizMode = !quizMode;
    $('toggle-quiz-mode').classList.toggle('quiz-mode');
    displayExample(currentExampleIndex);
    $('quiz-feedback').textContent = '';
    $('quiz-input').classList.remove('correct', 'incorrect');
    $('quiz-input').dispatchEvent(new Event('input'));
}

function handleKeyDown(e) {
    if (e.key === 'ArrowRight') nextExample();
    if (e.key === 'ArrowLeft') prevExample();
}