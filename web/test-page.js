// Opens dist/index.html from the disk in Chromium, runs every example, and
// checks the results, the errors and the Stop button.
// Usage: [PAGE_URL=...] node test-page.js [screenshot directory]
const path = require("path");
const { chromium } = require("playwright");

// PAGE_URL tests another copy, for example the desktop program.
const pageUrl = process.env.PAGE_URL || "file://" + path.resolve(__dirname, "dist/index.html");
const shots = process.argv[2];

async function finished(page) {
  await page.waitForFunction(() => /^(Finished|Stopped)/.test(document.getElementById("status").textContent), null, { timeout: 120000 });
  return page.textContent("#status");
}

async function ready(page) {
  await page.waitForFunction(() => document.getElementById("status").textContent === "Ready.", null, { timeout: 30000 });
}

(async () => {
  const browser = await chromium.launch();
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  const problems = [];
  page.on("console", (m) => { if (m.type() === "error") problems.push(m.text()); });
  page.on("pageerror", (e) => problems.push(String(e)));
  await page.goto(pageUrl);
  await ready(page);

  const expected = {
    0: ["true : x1^2 - x1", "x1 < x2 : x2 - x1"],
    3: ["x1 < x2 & le(x1, x2) : x2 - x1", "x1 < x2 & meet(x1, x2) < x1 : x2 - x1"],
  };
  const examples = await page.$$(".example");
  for (const [i, example] of examples.entries()) {
    for (const algorithm of ["colouring", "one-colour"]) {
      await page.check(`input[name="algorithm"][value="${algorithm}"]`);
      await example.click();
      const status = await finished(page);
      const orbits = await page.$$eval(".orbits li", (items) => items.map((li) => li.textContent));
      const errors = await page.$$eval(".errors li", (items) => items.map((li) => li.textContent));
      console.log(`example ${i} ${algorithm}: ${status} ${JSON.stringify(orbits.length ? orbits : errors)}`);
      if (expected[i] && JSON.stringify([...orbits].sort()) !== JSON.stringify(expected[i])) {
        throw new Error(`example ${i}: unexpected basis ${JSON.stringify(orbits)}`);
      }
      if (i === 5 && !(errors.length === 1 && errors[0].startsWith("Line 1: the description allows several orbits"))) {
        throw new Error("example 5: the error is not reported");
      }
    }
  }

  // Stop a long computation, then compute again.
  await page.check('input[name="algorithm"][value="colouring"]');
  await page.selectOption("#theory", "tree");
  await page.fill("#generators", "x < y & y < z & !le(x, y) & !le(y, z) & meet(x, y) = meet(y, z) : x*y*z - x - y - z");
  await page.fill("#limit", "100000");
  await page.click("#compute");
  await page.waitForTimeout(1500);
  const before = await page.textContent("#status");
  await page.click("#stop");
  console.log("stop: " + before + " -> " + (await page.textContent("#status")));
  await ready(page);
  await examples[0].click();
  console.log("after stop: " + (await finished(page)));

  if (shots) {
    await examples[3].click();
    await finished(page);
    await page.screenshot({ path: path.join(shots, "desktop.png"), fullPage: true });
    await page.setViewportSize({ width: 390, height: 844 });
    await page.screenshot({ path: path.join(shots, "phone.png"), fullPage: true });
    await page.emulateMedia({ colorScheme: "dark" });
    await page.setViewportSize({ width: 1280, height: 900 });
    await page.screenshot({ path: path.join(shots, "dark.png") });
  }
  if (problems.length) throw new Error("console errors: " + problems.join("; "));
  await browser.close();
  console.log("all checks passed");
})().catch((e) => { console.error(e); process.exit(1); });
