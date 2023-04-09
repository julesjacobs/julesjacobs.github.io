document.addEventListener('DOMContentLoaded', function() {
  // Get all the CSS rules from all the stylesheets
  const allRules = Array.from(document.styleSheets).reduce((rules, sheet) => {
    try {
      const sheetRules = sheet.cssRules ? Array.from(sheet.cssRules) : [];
      return [...rules, ...sheetRules];
    } catch (error) {
      console.warn(`Could not read CSS rules from ${sheet.href}: ${error.message}`);
      return rules;
    }
  }, []);

  // Get all the unused CSS rules
  const unusedRules = allRules.filter((rule) => !document.querySelector(rule.selectorText));

  // Log the unused rules to the console
  console.log('Unused CSS Rules:', unusedRules);
});