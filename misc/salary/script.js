document.addEventListener('DOMContentLoaded', () => {
    // Remove annualSalaryInput
    // const annualSalaryInput = document.getElementById('annual-salary');
    const tickerDisplay = document.getElementById('ticker');
    // Get references to editable rate spans
    const rateYearDisplay = document.getElementById('rate-year');
    const rateMonthDisplay = document.getElementById('rate-month');
    const rateWeekDisplay = document.getElementById('rate-week');
    const rateDayDisplay = document.getElementById('rate-day');
    const rateHourDisplay = document.getElementById('rate-hour');
    const rateMinuteDisplay = document.getElementById('rate-minute');
    const rateSecondDisplay = document.getElementById('rate-second');

    const spendAmountInput = document.getElementById('spend-amount');
    const timeToEarnDisplay = document.getElementById('time-to-earn');
    const spendButton = document.getElementById('spend-button');

    let annualSalary = 0;
    let earningsPerSecond = 0;
    let currentEarnings = 0;
    let tickerInterval = null;
    let isEditing = false; // Flag to prevent recursive updates

    // Keep constants
    const WEEKS_PER_YEAR = 52;
    const HOURS_PER_WEEK = 40;
    const DAYS_PER_WEEK = 5;
    const HOURS_PER_DAY = 8;
    const MINUTES_PER_HOUR = 60;
    const SECONDS_PER_MINUTE = 60;
    const SECONDS_PER_HOUR = SECONDS_PER_MINUTE * MINUTES_PER_HOUR;
    const SECONDS_PER_DAY = SECONDS_PER_HOUR * HOURS_PER_DAY;
    const SECONDS_PER_WEEK = SECONDS_PER_DAY * DAYS_PER_WEEK;
    const SECONDS_PER_YEAR_WORKING = SECONDS_PER_WEEK * WEEKS_PER_YEAR;
    const MONTHS_PER_YEAR = 12;
    const APPROX_SECONDS_PER_MONTH = SECONDS_PER_YEAR_WORKING / MONTHS_PER_YEAR;

    // --- Rate Update Logic ---

    function updateAllRates(sourceElementId, sourceValue) {
        if (isEditing) return; // Prevent updates while processing an edit

        let newAnnualSalary = 0;
        const value = parseFloat(sourceValue);
        if (isNaN(value) || value < 0) {
            // Handle invalid input - maybe reset to 0 or previous value?
            // For now, let's calculate based on 0
        } else {
            // Calculate annual salary based on which field was edited
            switch (sourceElementId) {
                case 'rate-year':
                    newAnnualSalary = value;
                    break;
                case 'rate-month':
                    newAnnualSalary = value * MONTHS_PER_YEAR;
                    break;
                case 'rate-week':
                    newAnnualSalary = value * WEEKS_PER_YEAR;
                    break;
                case 'rate-day':
                    newAnnualSalary = value * DAYS_PER_WEEK * WEEKS_PER_YEAR;
                    break;
                case 'rate-hour':
                    newAnnualSalary = value * HOURS_PER_WEEK * WEEKS_PER_YEAR;
                    break;
                case 'rate-minute':
                    newAnnualSalary = value * MINUTES_PER_HOUR * HOURS_PER_WEEK * WEEKS_PER_YEAR;
                    break;
                case 'rate-second':
                    newAnnualSalary = value * SECONDS_PER_HOUR * HOURS_PER_WEEK * WEEKS_PER_YEAR;
                    break;
                default:
                    console.error('Unknown rate element ID:', sourceElementId);
                    return; // Exit if source unknown
            }
        }

        annualSalary = newAnnualSalary;

        // Calculate all rates based on the new annual salary
        if (annualSalary > 0 && SECONDS_PER_YEAR_WORKING > 0) {
            earningsPerSecond = annualSalary / SECONDS_PER_YEAR_WORKING;
            const earningsPerMinute = earningsPerSecond * SECONDS_PER_MINUTE;
            const earningsPerHour = earningsPerMinute * MINUTES_PER_HOUR;
            const earningsPerDay = earningsPerHour * HOURS_PER_DAY;
            const earningsPerWeek = earningsPerDay * DAYS_PER_WEEK;
            const earningsPerMonth = annualSalary / MONTHS_PER_YEAR;

            // Update display values, avoiding the source element
            isEditing = true; // Set flag
            if (sourceElementId !== 'rate-year') rateYearDisplay.textContent = annualSalary.toFixed(2);
            if (sourceElementId !== 'rate-month') rateMonthDisplay.textContent = earningsPerMonth.toFixed(2);
            if (sourceElementId !== 'rate-week') rateWeekDisplay.textContent = earningsPerWeek.toFixed(2);
            if (sourceElementId !== 'rate-day') rateDayDisplay.textContent = earningsPerDay.toFixed(2);
            if (sourceElementId !== 'rate-hour') rateHourDisplay.textContent = earningsPerHour.toFixed(2);
            if (sourceElementId !== 'rate-minute') rateMinuteDisplay.textContent = earningsPerMinute.toFixed(2);
            if (sourceElementId !== 'rate-second') rateSecondDisplay.textContent = earningsPerSecond.toFixed(4);
            isEditing = false; // Clear flag

        } else {
            // Reset all if salary is 0 or invalid
            earningsPerSecond = 0;
            isEditing = true; // Set flag
            if (sourceElementId !== 'rate-year') rateYearDisplay.textContent = '0.00';
            if (sourceElementId !== 'rate-month') rateMonthDisplay.textContent = '0.00';
            if (sourceElementId !== 'rate-week') rateWeekDisplay.textContent = '0.00';
            if (sourceElementId !== 'rate-day') rateDayDisplay.textContent = '0.00';
            if (sourceElementId !== 'rate-hour') rateHourDisplay.textContent = '0.00';
            if (sourceElementId !== 'rate-minute') rateMinuteDisplay.textContent = '0.00';
            if (sourceElementId !== 'rate-second') rateSecondDisplay.textContent = '0.0000';
            isEditing = false; // Clear flag
        }

        resetTicker();
        updateTimeToEarn();
    }

    // --- Ticker Logic (mostly unchanged) ---
    function startTicker() {
        if (tickerInterval) {
            clearInterval(tickerInterval);
        }
        if (earningsPerSecond > 0) {
            const updateInterval = 100; // Update every 100ms (10 times per second)
            const earningsPerInterval = earningsPerSecond / (1000 / updateInterval);
            tickerInterval = setInterval(() => {
                currentEarnings += earningsPerInterval; // Add smaller amount more frequently
                tickerDisplay.textContent = currentEarnings.toFixed(4);
            }, updateInterval);
        }
    }

    function resetTicker() {
        if (tickerInterval) {
            clearInterval(tickerInterval);
            tickerInterval = null;
        }
        currentEarnings = 0;
        // Set initial ticker based on current precision, handle potential negative spend
        tickerDisplay.textContent = currentEarnings.toFixed(4);
        if (earningsPerSecond > 0) {
            startTicker();
        }
    }

    // --- Time to Earn Logic (mostly unchanged) ---
    function formatDuration(totalSeconds) {
        if (totalSeconds <= 0 || !isFinite(totalSeconds)) {
            return '---';
        }
        const WEEKS_PER_YEAR = 52;
        const HOURS_PER_WEEK = 40;
        const DAYS_PER_WEEK = 5;
        const HOURS_PER_DAY = 8;
        const MINUTES_PER_HOUR = 60;
        const SECONDS_PER_MINUTE = 60;
        const SECONDS_PER_HOUR = SECONDS_PER_MINUTE * MINUTES_PER_HOUR;
        const SECONDS_PER_DAY = SECONDS_PER_HOUR * HOURS_PER_DAY;

        const days = Math.floor(totalSeconds / SECONDS_PER_DAY);
        let remainingSeconds = totalSeconds % SECONDS_PER_DAY;

        const hours = Math.floor(remainingSeconds / SECONDS_PER_HOUR);
        remainingSeconds %= SECONDS_PER_HOUR;

        const minutes = Math.floor(remainingSeconds / SECONDS_PER_MINUTE);
        remainingSeconds %= SECONDS_PER_MINUTE;

        const seconds = Math.floor(remainingSeconds);

        let durationString = '';
        if (days > 0) durationString += `${days}d `;
        if (hours > 0) durationString += `${hours}h `;
        if (minutes > 0) durationString += `${minutes}m `;
        if (seconds >= 0 && totalSeconds < SECONDS_PER_MINUTE ) durationString += `${totalSeconds.toFixed(1)}s`; // Show decimals for small values
        else if (seconds > 0 || durationString === '') durationString += `${seconds}s`;

        return durationString.trim();
    }

    function updateTimeToEarn() {
        const spendAmount = parseFloat(spendAmountInput.value);
        if (isNaN(spendAmount) || spendAmount <= 0 || earningsPerSecond <= 0) {
            timeToEarnDisplay.textContent = '---';
            return;
        }

        const secondsToEarn = spendAmount / earningsPerSecond;
        timeToEarnDisplay.textContent = formatDuration(secondsToEarn);
    }

    // --- Event Listeners ---

    // Add listeners to editable rate spans
    const editableRates = document.querySelectorAll('.editable-rate');
    editableRates.forEach(span => {
        // Update calculations on input
        span.addEventListener('input', (event) => {
            const element = event.target;
            // Don't format here, just calculate
            const value = element.textContent.replace(/[^0-9.]/g, '');
            updateAllRates(element.id, value);
        });

        // Format the number correctly when the user finishes editing (blur)
        span.addEventListener('blur', (event) => {
            const element = event.target;
            const value = element.textContent.replace(/[^0-9.]/g, '');
            const numValue = parseFloat(value || 0);
            const precision = element.id === 'rate-second' ? 4 : 2;
            
            // Only update textContent if it differs to avoid triggering input event again
            const formattedValue = numValue.toFixed(precision);
            if (element.textContent !== formattedValue) {
                element.textContent = formattedValue;
            }
            // Recalculate one last time with the formatted value to ensure consistency
            // updateAllRates(element.id, formattedValue); // Might be redundant if input handled it
        });

        // Optional: Prevent line breaks on Enter key & trigger blur for formatting
        span.addEventListener('keydown', (event) => {
            if (event.key === 'Enter') {
                event.preventDefault();
                event.target.blur(); // Trigger update on Enter
            }
        });
         // Optional: Select all text on focus for easier editing
        span.addEventListener('focus', (event) => {
            window.setTimeout(() => {
                document.execCommand('selectAll', false, null);
            }, 0);
        });
    });

    // Remove listener for annualSalaryInput
    // annualSalaryInput.addEventListener('input', ...);

    spendAmountInput.addEventListener('input', updateTimeToEarn);

    spendButton.addEventListener('click', () => {
        const spendAmount = parseFloat(spendAmountInput.value);
        if (!isNaN(spendAmount) && spendAmount > 0) {
            currentEarnings -= spendAmount;
            tickerDisplay.textContent = currentEarnings.toFixed(4);
            // Don't clear spend input - user might want to reuse it
            // spendAmountInput.value = '';
            updateTimeToEarn(); // Keep time-to-earn updated
        } else {
            // spendAmountInput.value = '';
            updateTimeToEarn();
        }
    });

    // --- Initial Setup ---
    function initialize() {
        const initialYearlyRate = rateYearDisplay.textContent;
        updateAllRates('rate-year', initialYearlyRate);
        updateTimeToEarn(); // Ensure time-to-earn is calculated initially
    }

    initialize();

});


// Helper implementations for unchanged functions (for completeness)
function startTicker() {
    if (tickerInterval) {
        clearInterval(tickerInterval);
    }
    if (earningsPerSecond > 0) {
        const updateInterval = 100; // Update every 100ms (10 times per second)
        const earningsPerInterval = earningsPerSecond / (1000 / updateInterval);
        tickerInterval = setInterval(() => {
            currentEarnings += earningsPerInterval; // Add smaller amount more frequently
            tickerDisplay.textContent = currentEarnings.toFixed(4);
        }, updateInterval);
    }
}

function resetTicker() {
    if (tickerInterval) {
        clearInterval(tickerInterval);
        tickerInterval = null;
    }
    currentEarnings = 0;
    // Set initial ticker based on current precision, handle potential negative spend
    tickerDisplay.textContent = currentEarnings.toFixed(4);
    if (earningsPerSecond > 0) {
        startTicker();
    }
}

function formatDuration(totalSeconds) {
    if (totalSeconds <= 0 || !isFinite(totalSeconds)) {
        return '---';
    }
    const WEEKS_PER_YEAR = 52;
    const HOURS_PER_WEEK = 40;
    const DAYS_PER_WEEK = 5;
    const HOURS_PER_DAY = 8;
    const MINUTES_PER_HOUR = 60;
    const SECONDS_PER_MINUTE = 60;
    const SECONDS_PER_HOUR = SECONDS_PER_MINUTE * MINUTES_PER_HOUR;
    const SECONDS_PER_DAY = SECONDS_PER_HOUR * HOURS_PER_DAY;

    const days = Math.floor(totalSeconds / SECONDS_PER_DAY);
    let remainingSeconds = totalSeconds % SECONDS_PER_DAY;

    const hours = Math.floor(remainingSeconds / SECONDS_PER_HOUR);
    remainingSeconds %= SECONDS_PER_HOUR;

    const minutes = Math.floor(remainingSeconds / SECONDS_PER_MINUTE);
    remainingSeconds %= SECONDS_PER_MINUTE;

    const seconds = Math.floor(remainingSeconds);

    let durationString = '';
    if (days > 0) durationString += `${days}d `;
    if (hours > 0) durationString += `${hours}h `;
    if (minutes > 0) durationString += `${minutes}m `;
    if (seconds >= 0 && totalSeconds < SECONDS_PER_MINUTE ) durationString += `${totalSeconds.toFixed(1)}s`; // Show decimals for small values
    else if (seconds > 0 || durationString === '') durationString += `${seconds}s`;

    return durationString.trim();
}

function updateTimeToEarn() {
    const spendAmount = parseFloat(spendAmountInput.value);
    if (isNaN(spendAmount) || spendAmount <= 0 || earningsPerSecond <= 0) {
        timeToEarnDisplay.textContent = '---';
        return;
    }

    const secondsToEarn = spendAmount / earningsPerSecond;
    timeToEarnDisplay.textContent = formatDuration(secondsToEarn);
} 